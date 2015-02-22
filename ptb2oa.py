#!/usr/bin/env python

"""Convert Penn Treebank format into Open Annotation format.

Developed and tested only on the CRAFT corpus v1.0 treebank. Will
likely require some effort to work on other treebanks.
"""

import os
import sys
import codecs
import six
import json
import hashlib
import urlparse
import re

# python 2.5
import uuid

# Context description that is recommended for use in systems that
# implement the Open Annotation data model, copied Jan 2015 from
# http://www.openannotation.org/spec/core/publishing.html
oa_recommended_context = """\"oa": "http://www.w3.org/ns/oa#",
    "cnt": "http://www.w3.org/2011/content#",
    "dc": "http://purl.org/dc/elements/1.1/",
    "dcterms": "http://purl.org/dc/terms/",
    "dctypes": "http://purl.org/dc/dcmitype/",
    "foaf": "http://xmlns.com/foaf/0.1/",
    "rdf": "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
    "rdfs": "http://www.w3.org/2000/01/rdf-schema#",
    "skos": "http://www.w3.org/2004/02/skos/core#",
    "owl": "http://www.w3.org/2002/07/owl#",
    "prov": "http://www.w3.org/ns/prov#",
    "trig": "http://www.w3.org/2004/03/trix/rdfg-1/",
    "xsd": "http://www.w3.org/2001/XMLSchema#",

    "hasBody" :         {"@type":"@id", "@id" : "oa:hasBody"},
    "hasTarget" :       {"@type":"@id", "@id" : "oa:hasTarget"},
    "hasSource" :       {"@type":"@id", "@id" : "oa:hasSource"},
    "hasSelector" :     {"@type":"@id", "@id" : "oa:hasSelector"},
    "hasState" :        {"@type":"@id", "@id" : "oa:hasState"},
    "hasScope" :        {"@type":"@id", "@id" : "oa:hasScope"},
    "annotatedBy" :  {"@type":"@id", "@id" : "oa:annotatedBy"},
    "serializedBy" : {"@type":"@id", "@id" : "oa:serializedBy"},
    "motivatedBy" :  {"@type":"@id", "@id" : "oa:motivatedBy"},
    "equivalentTo" : {"@type":"@id", "@id" : "oa:equivalentTo"},
    "styledBy" :     {"@type":"@id", "@id" : "oa:styledBy"},
    "cachedSource" : {"@type":"@id", "@id" : "oa:cachedSource"},
    "conformsTo" :   {"@type":"@id", "@id" : "dcterms:conformsTo"},
    "default" :      {"@type":"@id", "@id" : "oa:default"},
    "item" :         {"@type":"@id", "@id" : "oa:item"},
    "first":         {"@type":"@id", "@id" : "rdf:first"},
    "rest":          {"@type":"@id", "@id" : "rdf:rest", "@container" : "@list"},

    "annotatedAt" :  { "@type": "xsd:dateTimeStamp", "@id": "oa:annotatedAt" },
    "end" :          { "@type": "xsd:nonNegativeInteger", "@id": "oa:end" },
    "exact" :        "oa:exact",
    "prefix" :       "oa:prefix",
    "serializedAt" : { "@type": "xsd:dateTimeStamp", "@id": "oa:serializedAt" },
    "start" :        { "@type": "xsd:nonNegativeInteger", "@id": "oa:start" },
    "styleClass" :   "oa:styleClass",
    "suffix" :       "oa:suffix",
    "when" :         { "@type": "xsd:dateTimeStamp", "@id": "oa:when" },

    "chars" :        "cnt:chars",
    "bytes" :        "cnt:bytes",
    "format" :       "dc:format",
    "language" :     "dc:language",
    "value" :        "rdf:value",
    "label" :        "rdfs:label",
    "name" :         "foaf:name",
    "mbox" :         "foaf:mbox\""""

# Compact OA context: minimal subset of the above (+oaAnn)
compact_oa_context = """\"oa": "http://www.w3.org/ns/oa#",
    "oaAnn": "http://www.w3.org/ns/oa#Annotation",
    "hasBody" :      { "@type": "@id", "@id": "oa:hasBody" },
    "hasTarget" :    { "@type": "@id", "@id": "oa:hasTarget" },
    "annotatedBy" :  { "@type": "@id", "@id": "oa:annotatedBy" },
    "serializedBy" : { "@type": "@id", "@id": "oa:serializedBy" },
    "annotatedAt" :  { "@type": "xsd:dateTimeStamp", "@id": "oa:annotatedAt" },
    "serializedAt" : { "@type": "xsd:dateTimeStamp", "@id": "oa:serializedAt" }"""

# URIs for PTB tags
PTB_URI_ROOT = 'http://purl.nlplab.org/ptb/'
POS_ROOT = PTB_URI_ROOT + 'pos#'
PTAG_ROOT = PTB_URI_ROOT + 'ptag#'
FTAG_ROOT = PTB_URI_ROOT + 'ftag#'

# Local prefixes for compact output
compact_prefix_map = {
    'http://craft.ucdenver.edu/annotation/': 'ann',
    'http://compbio.ucdenver.edu/': 'ucdenver',
    'http://bionlp-corpora.sourceforge.net/CRAFT/1.0/': 'craft',
    'http://example.org/ptb/': 'ptb',
    POS_ROOT: 'pos',
    PTAG_ROOT: 'ptag',
    FTAG_ROOT: 'ftag',
}

# Compact context: compact OA context and local prefixes
compact_context = ',\n'.join(
    [compact_oa_context] +
    ['    "%s": "%s"' % (p, f) for f, p in compact_prefix_map.items()]
    )

DEFAULT_ENCODING='utf-8'

TOKEN_REGEX = re.compile(r'([()]|[^()\s]+)')

DOCUMENT_ID_ROOT = 'http://bionlp-corpora.sourceforge.net/CRAFT/1.0/'
ANNOTATION_ID_ROOT = 'http://craft.ucdenver.edu/annotation/'
ANNOTATOR_ID = 'http://compbio.ucdenver.edu/Hunter_lab'

LEFT_PAREN = '('
RIGHT_PAREN = ')'

# OA constats
oa_id = '@id'
oa_type = '@type'
oa_context = '@context'
oa_default_type = 'oa:Annotation'
oa_compact_type = 'oaAnn'
oa_hasTarget = 'hasTarget'
oa_hasBody = 'hasBody'
oa_annotatedAt = 'annotatedAt'
oa_annotatedBy = 'annotatedBy'
oa_hasSource = 'hasSource'
oa_hasSelector = 'hasSelector'
oa_start = 'start'
oa_end = 'end'

# PTB-related constants
ptb_hasFtag = 'http://example.org/ptb/ftag'
ptb_hasIndex = 'http://example.org/ptb/index'
ptb_hasEqIndex = 'http://example.org/ptb/eqindex'
ptb_hasConstituent = 'http://example.org/ptb/constituent'

# feature category constants
POS_TAG, PHRASE_TAG, FUNCTIONAL_TAG, INDEX_NUMBER, EQUAL_INDEX = range(5)

def argparser():
    import argparse
    parser = argparse.ArgumentParser()

    parser.add_argument('-c', '--compact', action='store_true', default=False,
                        help='Compact output')
    parser.add_argument('-d', '--textdir', metavar='DIR', default=None,
                        help='Directory with text files')
    parser.add_argument('-e', '--expand-frag', action='store_true',
                        default=False, help='Expand fragment selectors')
    parser.add_argument('-l', '--limit-id', metavar='N', type=int, default=10,
                        help='Limit annotation IDs to N characters')
    parser.add_argument('-r', '--random-ids', action='store_true',
                        default=False, help='Random UUIDs')
    parser.add_argument('file', metavar='FILE', nargs='+',
                        help='Knowtator XML file to convert')

    return parser

def tokenize(line):
    for m in TOKEN_REGEX.finditer(line):
        yield(m.group(1))

def _is_string(s):
    return isinstance(s, six.string_types) and s not in '()'

def _has_word(stack):
    return (len(stack) >= 3 and stack[-3] == LEFT_PAREN and
            _is_string(stack[-2]) and _is_string(stack[-1]))

def rindex(list_, item):
    return list_[::-1].index(item)          

class Node(object):
    def words(self):
        raise NotImplementedError

    def nonterminals(self):
        raise NotImplementedError

    def traverse(self):
        raise NotImplementedError

    def span(self):
        raise NotImplementedError

    def features(self):
        raise NotImplementedError

    def children(self):
        raise NotImplementedError

    def is_empty(self):
        raise NotImplementedError

    def remove_empties(self):
        raise NotImplementedError
    
    @classmethod
    def from_stack(cls, stack):
        raise NotImplementedError

ptb_unescape = {
    '-LRB-' : '(',
    '-RRB-' : ')',
}

def unescape(s):
    return ptb_unescape.get(s, s)

def parse_label(label):
    """Parse PTB II label, returning its parts. A PTB II label
    consists of at least the syntactic label (e.g. "NP") and may have
    other tags (e.g. "SBAR-NOM-SBJ-2=4")."""
    # special case fix for Craft corpus
    if label == 'S-TTL-3-FRM':
        print >> sys.stderr, 'Note: rewriting label "S-TTL-3-FRM"'
        label = 'S-TTL-FRM-3'
    m = re.match(r'^([A-Z]+)(?:-([A-Z]+)(?:-([A-Z]+))?)?(?:-([0-9]+))?(?:=([0-9]+))?$', label)
    assert m, 'Failed to parse label %s' % label
    return m.groups()

class Word(Node):
    def __init__(self, form, tag):
        if any(c for c in form if c.isspace()):
            print >> sys.stderr, 'Warning: space in form: "%s"' % form
            form = form.strip()
        if tag != '-NONE-':
            self.form = unescape(form)
            self.tag = unescape(tag)
            self.ecat = None
        else:
            self.form = ''
            self.tag = tag
            self.ecat = form
        self.start = 0
        self.end = 0

    def words(self):
        yield self

    def nonterminals(self):
        return []

    def traverse(self):
        yield self

    def children(self):
        return []

    def is_empty(self):
        return self.form.strip() == '' and not self.tag == '-NONE-'

    def remove_empties(self):
        pass

    def span(self):
        return (self.start, self.end)

    def features(self):
        # TODO: ecat
        return { POS_TAG: self.tag }

    def __unicode__(self):
        return u'%s/%s' % (self.form, self.tag)

    @classmethod
    def from_stack(cls, stack):
        form = stack.pop()
        tag = stack.pop()
        assert stack.pop() == LEFT_PAREN
        return cls(form, tag)

class Nonterminal(Node):
    def __init__(self, label, children):
        self.label = label
        self._children = list(children)

    def words(self):
        for c in self._children:
            for w in c.words():
                yield w

    def nonterminals(self):
        yield self
        for c in self._children:
            for n in c.nonterminals():
                yield n

    def traverse(self):
        yield self
        for c in self._children:
            for n in c.traverse():
                yield n

    def children(self):
        return self._children

    def is_empty(self):
        return False

    def remove_empties(self):
        filtered = []
        for c in self._children:
            if not c.is_empty():
                c.remove_empties()
                filtered.append(c)
            else:
                print >> sys.stderr, 'Warning: removing empty: %s' % unicode(c)
                pass
        self._children = filtered

    def span(self):
        words = list(self.words())
        return (words[0].span()[0], words[-1].span()[1])

    def features(self):
        if self.label == '':
            return {}
        parts = parse_label(self.label)
        # phrase tag (e.g. "NP")
        feats = { PHRASE_TAG: parts[0] }
        # functional tags (e.g. "-SBJ")
        for i in (1,2):
            if parts[i] is not None:
                feats[FUNCTIONAL_TAG] = feats.get(FUNCTIONAL_TAG, []) + [parts[i]]
        # indices (e.g. "-1", "=2")
        if parts[3] is not None:
            feats[INDEX_NUMBER] = parts[3]
        if parts[4] is not None:
            feats[EQUAL_INDEX] = parts[4]
        # avoid feature lists of length 1
        if FUNCTIONAL_TAG in feats and len(feats[FUNCTIONAL_TAG]) == 1:
            feats[FUNCTIONAL_TAG] = feats[FUNCTIONAL_TAG][0]
        return feats
    
    @classmethod
    def from_stack(cls, stack):
        items = []
        item = stack.pop()
        while item != LEFT_PAREN:
            items.append(item)
            item = stack.pop()
        if _is_string(items[-1]):
            return cls(items[-1], reversed(items[:-1]))
        else:
            return cls('', reversed(items))

    def __unicode__(self):
        return u'<%s ' % self.label + u' '.join(str(c) for c in self._children) + u'>'

def parse(input, options=None):
    if isinstance(input, six.string_types):
        with codecs.open(input, encoding=DEFAULT_ENCODING) as f:
            return parse(f, options)

    stack, sentences = [], []
    for line in input:
        for token in tokenize(line):
            if token != RIGHT_PAREN:
                stack.append(token)
            elif _has_word(stack):
                stack.append(Word.from_stack(stack))
            else:
                c = Nonterminal.from_stack(stack)
                if not stack:
                    sentences.append(c)
                else:
                    stack.append(c)                    
    return sentences

def document_id(ann_fn):
    return DOCUMENT_ID_ROOT + os.path.splitext(os.path.basename(ann_fn))[0]

def get_document_text(ann_fn, options=None):
    # Text file should be in same directory as annotation by default,
    # other dirs can be given as options.
    text_dir = os.path.dirname(ann_fn)
    if options is not None and options.textdir is not None:
        text_dir = options.textdir
    text_fn = os.path.splitext(os.path.basename(ann_fn))[0] + '.txt'
    fn = os.path.join(text_dir, text_fn)
    try:
        with codecs.open(fn, encoding=DEFAULT_ENCODING) as f:
            return f.read()
    except IOError, e:
        raise IOError('Failed to find text file for %s: %s' % (ann_fn, fn))

def normalize_form(word, text):
    if word.form == '``' and text[0] == '"':
        word.form = '"'
    elif word.form == "''" and text[0] == '"':
        word.form = '"'

def set_offsets(sentences, text):
    """Align sentence words with text, setting start and end offsets."""
    off = 0
    for s in sentences:
        for w in s.words():
            while off < len(text) and text[off].isspace():
                off += 1
            wtext = text[off:off+len(w.form)]
            if wtext != w.form:
                normalize_form(w, text[off:])
                wtext = text[off:off+len(w.form)]
            assert wtext == w.form, \
                'Text mismatch:\n"%s" vs.\n"%s" (context: "%s")' % \
                (wtext.encode('utf-8'), w.form.encode('utf-8'),
                 text[max(0,off-30):min(len(text),off+len(w.form)+30)].encode('utf-8'))
            w.start, w.end = off, off+len(w.form)
            off += len(w.form)

def parse_frag(frag):
    # parse rfc5147 text/plain chracter range fragment identifier
    # (TODO others)
    m = re.match(r'^char=(\d+),(\d+)$', frag)
    if not m:
        raise ValueError('failed to parse fragment %s' % frag)
    start, end = m.groups()
    try:
        return int(start), int(end)
    except ValueError:
        raise ValueError('failed to parse fragment %s' % frag)

def expand_fragment(target):
    url, frag = urlparse.urldefrag(target)
    start, end = parse_frag(frag)
    return {
        oa_hasSource : url,
        oa_hasSelector : {
            oa_start: start,
            oa_end: end
        },
    }

def expand_fragments(document):
    tgt = document[oa_hasTarget]
    if isinstance(tgt, six.string_types):
        tgt = expand_fragment(tgt)
    else:
        assert isinstance(tgt, list)
        tgt = [expand_fragment(t) for t in tgt]
    document[oa_hasTarget] = tgt
    return document

def sha1(s):
    return hashlib.sha1(s).hexdigest()

def create_document(node, document_id, options=None):
    if not options or not options.compact:
        oa_type_value = oa_default_type
    else:
        oa_type_value = oa_compact_type
    return {
        oa_type:        oa_type_value,
        oa_hasTarget: document_id + '#char=%d,%d' % node.span(),
        oa_hasBody: dict([map_feature(k, v) for k, v in node.features().items()]),
        oa_annotatedBy: ANNOTATOR_ID,
    }

def create_id(document, options=None):
    if options is not None and not options.random_ids:
        # exclude ID if present to keep ID stable over assignment
        document = document.copy()
        try:
            del document[oa_id]
        except KeyError:
            pass
        # TODO: consider expanding JSON-LD
        serialized = json.dumps(document, separators=(',',':'), sort_keys=True)
        id_ = sha1(serialized)
    else:
        id_ = str(uuid.uuid4()) # random uuid as default
    if options is not None and options.limit_id is not None:
        id_ = id_[:options.limit_id]
    return ANNOTATION_ID_ROOT + id_    

def body_id(id_):
    #return id_ + '-b'
    return None # no body ID

integer_feature = set([
        INDEX_NUMBER,
        EQUAL_INDEX,
])

key_uri = {
    POS_TAG: oa_type,    
    PHRASE_TAG: oa_type,    
    FUNCTIONAL_TAG: ptb_hasFtag,
    INDEX_NUMBER: ptb_hasIndex,
    EQUAL_INDEX: ptb_hasEqIndex,
}

key_root = {
    POS_TAG: POS_ROOT,
    PHRASE_TAG: PTAG_ROOT,
    FUNCTIONAL_TAG: FTAG_ROOT,
}

URI_escape = {
    '(' : 'LRB',
    ')' : 'RRB',
    '``': 'LQUOT',
    "''": 'RQUOT',
    ',' : 'COMMA',
    '.' : 'PERIOD',
    ':' : 'COLON',
    'PRP$' : 'PRP-POSS',
    'WP$' : 'WP-POSS',
}

# http://tools.ietf.org/html/rfc3986#section-2.3
ALPHA = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'
DIGIT = '0123456789'
URI_unreserved_characters = set(ALPHA + DIGIT + '-._~')

def escape_URI(value):
    value = URI_escape.get(value, value)
    if any(c for c in value if c not in URI_unreserved_characters):
        print >> sys.stderr, 'Warning: reserved char in value: "%s"' % value
    return value

def add_root(root, value):
    if isinstance(value, six.string_types):
        return root + value
    else:
        assert isinstance(value, list)
        return [root + v for v in value]    

def map_feature(key, value):
    if isinstance(value, six.string_types):
        value = escape_URI(value)
    else:
        assert isinstance(value, list)
        value = [escape_URI(v) for v in value]
    if key in integer_feature:
        return (key_uri[key], int(value))
    try:
        return (key_uri[key], add_root(key_root[key], value))
    except KeyError:
        assert False, "Don't know how to map %s" % key
    
def tag_type(tag):
    return POS_ROOT + tag

def compact_string(s, prefix_map):
    for pref, short in prefix_map.items():
        if s == pref:
            return short
        elif s.startswith(pref):
            return '%s:%s' % (short, s[len(pref):])
    return s

def compact(document, prefix_map=None):
    if prefix_map is None:
        prefix_map = compact_prefix_map
    compacted = {}
    for key, val in document.items():        
        if isinstance(val, six.string_types):
            val = compact_string(val, prefix_map)
        elif isinstance(val, list):
            val = [compact_string(v, prefix_map) for v in val]
        elif isinstance(val, dict):
            val = compact(val, prefix_map)
        elif isinstance(val, int):
            pass
        else:
            print >> sys.stderr, 'Warning: unexpected type to compact', val
            pass
        key = compact_string(key, prefix_map)
        compacted[key] = val
    return compacted

def convert(ann_fn, sentences, options=None):
    out = codecs.getwriter(DEFAULT_ENCODING)(sys.stdout)
    
    text = get_document_text(ann_fn, options)
    set_offsets(sentences, text)

    doc_id = document_id(ann_fn)

    converted = []
    for s in sentences:
        # assign IDs to all nodes everything first for references
        for n in s.traverse():
            n.id = create_id(create_document(n, doc_id, options), options)
        for n in s.traverse():
            document = create_document(n, doc_id, options)
            document[oa_id] = n.id
            if n.children():
                if len(n.children()) == 1:
                    cons = n.children()[0].id
                else:
                    cons = [c.id for c in n.children()]
                document[oa_hasBody][ptb_hasConstituent] = cons
            bod_id = body_id(document[oa_id])
            if bod_id:
                document[oa_hasBody][oa_id] = bod_id
            converted.append(document)
    if options and options.expand_frag:
        converted = [expand_fragments(c) for c in converted]
    if options and options.compact:
        converted = [compact(c) for c in converted]
    return converted

def pretty_print(doc, initial_indent=0):
    s = json.dumps(doc, sort_keys=True, indent=2, separators=(',', ': '))
    if initial_indent == 0:
        return s
    else:
        idt = ' ' * initial_indent
        return idt + s.replace('\n', '\n'+idt)

def write_header(out, options=None, context=None):
    if context is None:
        if options is None or not options.compact:
            context = oa_recommended_context
        else:
            context = compact_context

    print >> out, '''{
  "@context": {
    %s
  },
  "@graph": [''' % context

def write_footer(out):
    print >> out, '''
  ]
}'''

def process(fn, options=None, is_first=True):
    try:
        sentences = parse(fn, options)
    except:
        print >> sys.stderr, 'Failed to parse %s' % fn
        raise
    for s in sentences:
        s.remove_empties()
    out = sys.stdout
    for i, c in enumerate(convert(fn, sentences, options)):
        if not is_first or i != 0:
            out.write(',\n')
        out.write(pretty_print(c, 5))

def main(argv):
    args = argparser().parse_args(argv[1:])

    write_header(sys.stdout, args)
    for i, fn in enumerate(args.file):
        process(fn, args, i==0)
    write_footer(sys.stdout)

    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv))
