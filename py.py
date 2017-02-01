class Sym:
    tag = 'sym'
    def __init__(self, V): self.val = V ; self.nest = []
    def __iadd__(self,o): return self.push(o)
    def push(self,o): self.nest.append(o) ; return self
    def __repr__(self): return self.head()
    def head(self): return '<%s:%s>' % (self.tag, self.val)
    def dump(self, depth=0):
        S = '\n' + '\t' * depth + self.head()
        for i in self.nest: S += i.dump(depth+1)
        return S
class Str(Sym):
    tag = 'str'
    def head(self): return '<%s:\'%s\'>' % (self.tag, self.val)
class Url(Sym): tag = 'url'
class Vector(Sym):
    tag = 'vector'
    def __init__(self): Sym.__init__(self, '')
    def head(self): return '[]'
class Op(Sym):
    tag = 'op'
    def head(self): return self.val
class Dep(Sym):
    tag = 'dep'
    def __init__(self): Sym.__init__(self, '')

import sys
import ply.lex  as lex
import ply.yacc as yacc

tokens = [ 'SYM' , 'STR' , 'URL' ,
            'LP' , 'RP' , 'LQ' , 'RQ' , #'LC' , 'RC' ,
            'OP' , 'EQ' , 'AT' , 'TILD' , 'COMMA' ,
            'ADD' , 'SUB' , 'MUL' , 'DIV' , 'POW' , 'DEPL','DEPR' ]

states = [
    ('str','exclusive'),
    ('end','exclusive')
    ]

t_ignore_comment = r'\#.*'
t_ignore = ' \t\r'
def t_newline(t):
    r'\n'
    t.lexer.lineno += 1
    
def t_END(t):
    r'\.end'
    t.lexer.begin('end')
t_end_ignore = '.\n'
def t_end_any(t): r'.'    
    
t_str_ignore = ''
def t_STR(t):
    r'\''
    t.lexer.begin('str')
    t.lexer.str = ''
def t_str_STR(t):
    r'\''
    t.lexer.begin('INITIAL')
    t.value = Str(t.lexer.str) ; return t
def t_str_CHAR(t):
    r'.'
    t.lexer.str += t.value
    
def t_URL(t):
    r'[a-z]+:[a-z/.]+'
    t.value = Url('\'%s\''%t.value) ; return t
def t_SYM(t):
    r'[a-zA-Z0-9_.]+'
    t.value = Sym(t.value) ; return t

def t_LP(t):
    r'\('
    return t_OP(t)
def t_RP(t):
    r'\)'
    return t_OP(t)
def t_LQ(t):
    r'\['
    return t_OP(t)
def t_RQ(t):
    r'\]'
    return t_OP(t)
def t_LC(t):
    r'\{'
    return t_OP(t)
def t_RC(t):
    r'\}'
    return t_OP(t)
def t_DEPL(t):
    r':<'
    return t_OP(t)
def t_DEPR(t):
    r'>:'
    return t_OP(t)

def t_EQ(t):
    r'\='
    return t_OP(t)
def t_AT(t):
    r'\@'
    return t_OP(t)
def t_TILD(t):
    r'\~'
    return t_OP(t)
def t_COMMA(t):
    r'\,'
    return t_OP(t)

def t_ADD(t):
    r'\+'
    return t_OP(t)
def t_SUB(t):
    r'\-'
    return t_OP(t)
def t_MUL(t):
    r'\*'
    return t_OP(t)
def t_DIV(t):
    r'\/'
    return t_OP(t)
def t_POW(t):
    r'\^'
    return t_OP(t)

def t_OP(t):
    r'[\:\;\<\>\$\&]'
    t.value = Op(t.value) ; return t

precedence = [
    ('left','ADD','SUB'),
    ('right','PFX')
    ]

def p_REPL_none(p):
    ' REPL : '
def p_REPL_recur(p):
    ' REPL : REPL ex '
    print p[2].dump()

def p_ex_scalar(p):
    ' ex : scalar '
    p[0] = p[1]
def p_scalar(p):
    ''' scalar : SYM
               | STR
               | URL
               | OP '''
    p[0] = p[1]

def p_parens(p):
    ' ex : LP ex RP '
    p[0] = p[2]
def p_ex_tild(p):
    ' ex : TILD ex '
    p[0] = p[1] ; p[0] += p[2]
def p_ex_eq(p):
    ' ex : ex EQ ex '
    p[0] = p[2] ; p[0] += p[1] ; p[0] += p[3]
def p_ex_at(p):
    ' ex : ex AT ex '
    p[0] = p[2] ; p[0] += p[1] ; p[0] += p[3]

def p_ex_pfx_add(p):
    ' ex : ADD ex %prec PFX '
    p[0] = p[1] ; p[0] += p[2]
def p_ex_pfx_sub(p):
    ' ex : SUB ex %prec PFX '
    p[0] = p[1] ; p[0] += p[2]

def p_ex_add(p):
    ' ex : ex ADD ex '
    p[0] = p[2] ; p[0] += p[1] ; p[0] += p[3]
def p_ex_sub(p):
    ' ex : ex SUB ex '
    p[0] = p[2] ; p[0] += p[1] ; p[0] += p[3]
def p_ex_mul(p):
    ' ex : ex MUL ex '
    p[0] = p[2] ; p[0] += p[1] ; p[0] += p[3]
def p_ex_div(p):
    ' ex : ex DIV ex '
    p[0] = p[2] ; p[0] += p[1] ; p[0] += p[3]
def p_ex_pow(p):
    ' ex : ex POW ex '
    p[0] = p[2] ; p[0] += p[1] ; p[0] += p[3]
    
def p_ex_vector(p):
    ' ex : LQ vector RQ '
    p[0] = p[2]
def p_vector_new(p):
    ' vector : '
    p[0] = Vector()
def p_vector_comma(p):
    ' vector : vector COMMA '
    p[0] = p[1]     
def p_vector_item(p):
    ' vector : vector ex '
    p[0] = p[1] ; p[0] += p[2]

def p_ex_dep(p):
    r' ex : ex DEPL ex DEPR ex '
    p[0] = Dep() ; p[0]+=p[1] ; p[0]+=p[3] ; p[0]+=p[5]

def t_ANY_error(t): print 'lexer/error', t
def p_error(p): print 'parse/error', p

lex.lex()
parse = yacc.yacc(debug=False, write_tables=False).parse(sys.stdin.read())
