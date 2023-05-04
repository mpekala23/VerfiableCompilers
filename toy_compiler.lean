import algebra
import data.real.basic
import data.vector
import tactic.explode
import tactic.find
import tactic.induction
import tactic.linarith
import tactic.rcases
import tactic.rewrite
import tactic.ring_exp
import tactic.tidy
import tactic.where

/-
Using https://github.com/blanchette/logical_verification_2020/blob/master/lean/lovelib.lean
-/

namespace LoVe


/- ## Structured Proofs -/

notation `fix ` binders `, ` r:(scoped f, f) := r


/- ## Logical Connectives -/

attribute [pattern] or.intro_left or.intro_right

meta def tactic.dec_trivial := `[exact dec_trivial]

lemma not_def (a : Prop) :
  ¬ a ↔ a → false :=
by refl

@[simp] lemma not_not_iff (a : Prop) [decidable a] :
  ¬¬ a ↔ a :=
by by_cases a; simp [h]

@[simp] lemma and_imp_distrib (a b c : Prop) :
  (a ∧ b → c) ↔ (a → b → c) :=
iff.intro
  (assume h ha hb, h ⟨ha, hb⟩)
  (assume h ⟨ha, hb⟩, h ha hb)

@[simp] lemma or_imp_distrib {a b c : Prop} :
  a ∨ b → c ↔ (a → c) ∧ (b → c) :=
iff.intro
  (assume h,
   ⟨assume ha, h (or.intro_left _ ha), assume hb, h (or.intro_right _ hb)⟩)
  (assume ⟨ha, hb⟩ h, match h with or.inl h := ha h | or.inr h := hb h end)

@[simp] lemma exists_imp_distrib {α : Sort*} {p : α → Prop} {a : Prop} :
  ((∃x, p x) → a) ↔ (∀x, p x → a) :=
iff.intro
  (assume h hp ha, h ⟨hp, ha⟩)
  (assume h ⟨hp, ha⟩, h hp ha)

lemma and_exists {α : Sort*} {p : α → Prop} {a : Prop} :
  (a ∧ (∃x, p x)) ↔ (∃x, a ∧ p x) :=
iff.intro
  (assume ⟨ha, x, hp⟩, ⟨x, ha, hp⟩)
  (assume ⟨x, ha, hp⟩, ⟨ha, x, hp⟩)

@[simp] lemma exists_false {α : Sort*} :
  (∃x : α, false) ↔ false :=
iff.intro (assume ⟨a, f⟩, f) (assume h, h.elim)


/- ## Natural Numbers -/

attribute [simp] nat.add


/- ## Integers -/

@[simp] lemma int.neg_comp_neg :
  int.neg ∘ int.neg = id :=
begin
  apply funext,
  apply neg_neg
end


/- ## Reflexive Transitive Closure -/

namespace rtc

inductive star {α : Sort*} (r : α → α → Prop) (a : α) : α → Prop
| refl {}    : star a
| tail {b c} : star b → r b c → star c

attribute [refl] star.refl

namespace star

variables {α : Sort*} {r : α → α → Prop} {a b c d : α}

@[trans] lemma trans (hab : star r a b) (hbc : star r b c) :
  star r a c :=
begin
  induction' hbc,
  case refl {
    assumption },
  case tail : c d hbc hcd hac {
    exact (tail (hac hab)) hcd }
end

lemma single (hab : r a b) :
  star r a b :=
refl.tail hab

lemma head (hab : r a b) (hbc : star r b c) :
  star r a c :=
begin
  induction' hbc,
  case refl {
    exact (tail refl) hab },
  case tail : c d hbc hcd hac {
    exact (tail (hac hab)) hcd }
end

lemma head_induction_on {α : Sort*} {r : α → α → Prop} {b : α}
  {P : ∀a : α, star r a b → Prop} {a : α} (h : star r a b)
  (refl : P b refl)
  (head : ∀{a c} (h' : r a c) (h : star r c b), P c h → P a (h.head h')) :
  P a h :=
begin
  induction' h,
  case refl {
    exact refl },
  case tail : b c hab hbc ih {
    apply ih,
    show P b _, from
      head hbc _ refl,
    show ∀a a', r a a' → star r a' b → P a' _ → P a _, from
      assume a a' hab hbc, head hab _ }
end

lemma trans_induction_on {α : Sort*} {r : α → α → Prop}
    {p : ∀{a b : α}, star r a b → Prop} {a b : α} (h : star r a b)
    (ih₁ : ∀a, @p a a refl) (ih₂ : ∀{a b} (h : r a b), p (single h))
    (ih₃ : ∀{a b c} (h₁ : star r a b) (h₂ : star r b c), p h₁ →
       p h₂ → p (h₁.trans h₂)) :
  p h :=
begin
  induction' h,
  case refl {
    exact ih₁ a },
  case tail : b c hab hbc ih {
    exact ih₃ hab (single hbc) (ih ih₁ @ih₂ @ih₃) (ih₂ hbc) }
end

lemma lift {β : Sort*} {s : β → β → Prop} (f : α → β)
  (h : ∀a b, r a b → s (f a) (f b)) (hab : star r a b) :
  star s (f a) (f b) :=
hab.trans_induction_on
  (assume a, refl)
  (assume a b, single ∘ h _ _)
  (assume a b c _ _, trans)

lemma mono {p : α → α → Prop} :
  (∀a b, r a b → p a b) → star r a b → star p a b :=
lift id

lemma star_star_eq :
  star (star r) = star r :=
funext
  (assume a,
   funext
     (assume b,
      propext (iff.intro
        (assume h,
         begin
           induction' h,
           { refl },
           { transitivity;
               assumption }
         end)
        (star.mono (assume a b,
           single)))))

end star

end rtc

export rtc


/- ## States -/

def state :=
string → ℕ

def state.update (name : string) (val : ℕ) (s : state) : state :=
λname', if name' = name then val else s name'

notation s `{` name ` ↦ ` val `}` := state.update name val s

instance : has_emptyc state :=
{ emptyc := λ_, 0 }

@[simp] lemma update_apply (name : string) (val : ℕ) (s : state) :
  s{name ↦ val} name = val :=
if_pos rfl

@[simp] lemma update_apply_ne (name name' : string) (val : ℕ) (s : state)
    (h : name' ≠ name . tactic.dec_trivial) :
  s{name ↦ val} name' = s name' :=
if_neg h

@[simp] lemma update_override (name : string) (val₁ val₂ : ℕ) (s : state) :
  s{name ↦ val₂}{name ↦ val₁} = s{name ↦ val₁} :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp [h]
end

@[simp] lemma update_swap (name₁ name₂ : string) (val₁ val₂ : ℕ) (s : state)
    (h : name₁ ≠ name₂ . tactic.dec_trivial) :
  s{name₂ ↦ val₂}{name₁ ↦ val₁} = s{name₁ ↦ val₁}{name₂ ↦ val₂} :=
begin
  apply funext,
  intro name',
  by_cases name' = name₁;
    by_cases name' = name₂;
    simp * at *
end

@[simp] lemma update_id (name : string) (s : state) :
  s{name ↦ s name} = s :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp * at *
end

example (s : state) :
  s{"a" ↦ 0}{"a" ↦ 2} = s{"a" ↦ 2} :=
by simp

example (s : state) :
  s{"a" ↦ 0}{"b" ↦ 2} = s{"b" ↦ 2}{"a" ↦ 0} :=
by simp

example (s : state) :
  s{"a" ↦ s "a"}{"b" ↦ 0} = s{"b" ↦ 0} :=
by simp


/- ## Relations -/

def Id {α : Type} : set (α × α) :=
{ab | prod.snd ab = prod.fst ab}

@[simp] lemma mem_Id {α : Type} (a b : α) :
  (a, b) ∈ @Id α ↔ b = a :=
by refl

def comp {α : Type} (r₁ r₂ : set (α × α)) : set (α × α) :=
{ac | ∃b, (prod.fst ac, b) ∈ r₁ ∧ (b, prod.snd ac) ∈ r₂}

infixl ` ◯ ` : 90 := comp

@[simp] lemma mem_comp {α : Type} (r₁ r₂ : set (α × α))
    (a b : α) :
  (a, b) ∈ r₁ ◯ r₂ ↔ (∃c, (a, c) ∈ r₁ ∧ (c, b) ∈ r₂) :=
by refl

def restrict {α : Type} (r : set (α × α)) (p : α → Prop) :
  set (α × α) :=
{ab | p (prod.fst ab) ∧ ab ∈ r}

infixl ` ⇃ ` : 90 := restrict

@[simp] lemma mem_restrict {α : Type} (r : set (α × α))
    (p : α → Prop) (a b : α) :
  (a, b) ∈ r ⇃ p ↔ p a ∧ (a, b) ∈ r :=
by refl

end LoVe

open LoVe

-- Arithmetic expressions in the while language
inductive aexp : Type
| N : ℕ -> aexp
| V : string -> aexp
| Plus : aexp -> aexp -> aexp

-- Boolean expressions in the while language
inductive bexp : Type
| Bc : bool -> bexp
| Not : bexp -> bexp
| And : bexp -> bexp -> bexp
| Less : aexp -> aexp -> bexp

-- Statements in the while language
inductive stmt : Type
| skip : stmt
| assign : string → aexp → stmt
| seq : stmt → stmt → stmt 
| ite : bexp → stmt → stmt → stmt
| while : bexp → stmt → stmt

-- Evaluating arithmetic
def aval : aexp -> LoVe.state -> ℕ 
| (aexp.N i) _ := i
| (aexp.V x) s := s x
| (aexp.Plus a b) s := (aval a s) + (aval b s)

-- Evaluating boolean expressions
def bval : bexp -> LoVe.state -> bool
| (bexp.Bc b) _ := b
| (bexp.Not x) s := not (bval x s)
| (bexp.And a b) s := (bval a s) ∧ (bval b s)
| (bexp.Less a b) s := (aval a s) < (aval b s) 

infixr ` ;; ` : 90 := stmt.seq

-- A step in the language
inductive big_step : stmt × LoVe.state → LoVe.state → Prop
| skip {s} :
big_step (stmt.skip, s) s
| assign {x a s} :
big_step (stmt.assign x a, s) (s{x ↦ aval a s})
| seq {S T s t u} (hS : big_step (S, s) t)
(hT : big_step (T, t) u) :
big_step (S ;; T, s) u
| ite_true {b : bexp} {S T s t} (hcond : bval b s)
(hbody : big_step (S, s) t) :
big_step (stmt.ite b S T, s) t
| ite_false {b : bexp} {S T s t} (hcond : ¬ bval b s)
(hbody : big_step (T, s) t) :
big_step (stmt.ite b S T, s) t
| while_true {b : bexp} {S s t u} (hcond : bval b s)
(hbody : big_step (S, s) t)
(hrest : big_step (stmt.while b S, t) u) :
big_step (stmt.while b S, s) u
| while_false {b : bexp} {S s} (hcond : ¬ bval b s) :
big_step (stmt.while b S, s) s

inductive instr : Type
| loadi : int → instr
| load : string → instr
| add : instr
| store : string → instr
| jmp : int → instr
| jmpless : int → instr
| jmpge : int → instr

notation `config` := int × state × list int
notation `program` := list instr

inductive iexec : instr -> config -> config -> Prop
| loadi {i s stk} (n : int):
iexec (instr.loadi n) (i,s, stk) (i + 1, s, n :: stk)
| load {i s stk} (x : string) :
iexec (instr.load x) (i, s, stk) (i + 1, s, s x :: stk)
| add {i s stk a b} :
iexec instr.add (i, s, a :: b :: stk) (i + 1, s, (a + b) :: stk)
| store {i s stk a} (x : string) :
iexec (instr.store x) (i, s, a :: stk) (i + 1, s{x 7→ a}, stk)
| jmp {i s stk} (n : int) :
iexec (instr.jmp n) (i,s, stk) (i + 1 + n, s, stk)
| jmpless_true {i s stk a b} (n : int) (hcond : b < a):
iexec (instr.jmpless n) (i,s , a :: b :: stk) (i + 1 + n, s, stk)
| jmpless_false {i s stk a b} (n : int) (hcond : ¬ b < a):
iexec (instr.jmpless n) (i, s, a :: b :: stk) (i + 1, s, stk)
| jmpge_true {i s stk a b} (n : int) (hcond : b ≥ a):
iexec (instr.jmpge n) (i,s , a :: b :: stk) (i + 1 + n, s, stk)
| jmpge_false {i s stk a b} (n : int) (hcond : ¬ b ≥ a):
iexec (instr.jmpge n) (i, s, a :: b :: stk) (i + 1, s, stk)

inductive exec1 : program -> config -> config -> Prop
| exec1 {p s stk c' x} {n : ℕ}
  (hnth : list.nth p n = some x )
  (hiexec : iexec x
    (n, s, stk)
    c'):
exec1 p (n, s, stk) c'

-- Compilation of an arithmetic expression
def acomp : aexp -> program
| (aexp.N i) := [instr.loadi i]
| (aexp.V x) := [instr.load x]
| (aexp.Plus a b) := (acomp a) ++ (acomp b) ++ [instr.add]

-- Compilation of a boolean expression
def bcomp : bexp -> bool -> int -> program
| (bexp.Bc v) f n := cond (v = f) [instr.jmp n] []
| (bexp.Not b) f n := bcomp b (!f) n
| (bexp.And b1 b2) f n :=
    let cb2 := bcomp b2 f n in
    let m := cond f (↑cb2.length) (↑cb2.length + n) in
    let cb1 := bcomp b1 ff m in
    cb1 ++ cb2
| (bexp.Less a1 a2) f n :=
    (acomp a1) ++ (acomp a2) ++ (cond f
    [instr.jmpless n]
    [instr.jmpge n])
  
-- Compilation of statement
def ccomp : stmt -> program
| (stmt.skip) := []
| (stmt.assign x a) := (acomp a) ++ [instr.store x]
| (stmt.seq a b) := (ccomp a) ++ (ccomp b)
| (stmt.ite b c1 c2) :=
  let cc1 := ccomp c1 in
  let cc2 := ccomp c2 in
  -- If b is false, jump over the = then"-clause
  let cb := bcomp b ff (( list.length cc1 ) + 1)
  -- The added jump instruction is there so that execution jumps over the
  -- "else"-clause after the "then"-clause is done.
  in cb ++ cc1 ++ [instr.jmp (list.length cc2)] ++ cc2
  | (stmt.while b c) :=
  let cc := ccomp c in
  -- If b is false, jump over the body
  let cb := bcomp b ff (list.length cc + 1)
  -- The added jump instruction is there so that execution jumps back to
  -- the condition after executing the body
  in cb ++ cc ++ [instr.jmp (- (list.length cb + list.length cc + 1) )]

-- The main theorem
theorem correct {c s t stk} :
big_step (c, s) t
↔
exec1 (ccomp c) (0, s, stk)
(↑(list.length (ccomp c)), t, stk) :=
begin
  sorry,
end

lemma correct {a s stk} :
exec1 (acomp a) (0, s, stk)
↑(list.length (acomp a),
s,
(aval a s) :: stk) :=
begin
  induction' a,
  case aexp.N : n {
  show (acomp (aexp.N n)) `
  (0, s, stk) ⇒*
  (↑(acomp (aexp.N n)).length,
  s,
  aval (aexp.N n) s :: stk),
  -- star.single takes an element of a relation =⇒ and creates the
  -- corresponding element of ⇒*
  exact star.single (exec1.exec1 (begin simp end) (iexec.loadi _)),
  },
  case aexp.V : x {
  show (acomp (aexp.V x)) `
  (0, s, stk) ⇒*
  (↑(acomp (aexp.V x)).length,
  s,
  aval (aexp.V x) s :: stk),
  exact star.single (exec1.exec1 (begin simp end) (iexec.load _)),
  },
  acomp a ++ acomp a_1 ++ [instr.add] `
  (0, s, stk) ⇒*
  (list.length (acomp a_1) + list.length (acomp a) + 1,
  s,
  (aval a_1 s + aval a s) :: stk)
  These are the induction hypotheses:
  acomp a `
  (0, s, stk) ⇒* (length (acomp a), s, aval a s :: stk)
  -- The initial stack is chosen to be aval a s :: stk
  acomp a_1 `
  (0, s, aval a s :: stk) ⇒*
  (0,
  s,
  aval a_1 s :: aval a s :: stk)
  -- acomp a_1 ++ [instr.add] appended to the right
  l := acomp a ++ acomp a_1 ++ [instr.add] `
    (0, s, stk) ⇒* (length (acomp a), s, aval a s :: stk)
  -- acomp a appended to the left, and [instr.add] appended to the right
  r := acomp a ++ acomp a_1 ++ [instr.add] `
    (length (acomp a),
    s,
    aval a s :: stk) ⇒*
    (length (acomp a_1) + length (acomp a),
    s,
    aval a_1 s :: aval a s :: stk)
  acomp a ++ acomp a_1 ++ [instr.add] `
    (0, s, stk) ⇒*
    (length (acomp a_1) + length (acomp a),
    s,
    aval a_1 s :: aval a s :: stk)
  [instr.add] `
    (0, s, aval a_1 s :: aval a s :: stk) ⇒*
    (1, s, (aval a_1 s + aval a s) :: stk)
    -- acomp a ++ acomp a_1 appended to the left
    acomp a ++ acomp a_1 ++ [instr.add] `
    (length (acomp a_1) + length (acomp a),
    s,
    aval_1 s :: aval a s :: stk) ⇒*
    (length (acomp a_1) + length (acomp a) + 1,
    s,
    (aval a_1 s + aval a s) stk)
  acomp a ++ acomp a_1 ++ [instr.add] `
    (0, s, stk) ⇒*
    (length (acomp a_1) + length (acomp a) + 1,
    s,
    (aval a_1 s + aval a s) :: stk)
  sorry,
end