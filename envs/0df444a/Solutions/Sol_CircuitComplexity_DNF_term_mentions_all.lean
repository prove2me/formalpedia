-- Prove2me | solution 1 for CircuitComplexity.DNF.term_mentions_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:43.102878+00:00
-- url     : https://prove2.me/submissions/f3c6e5c2-832a-492a-94fa-50bf8752906c

module
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_NF
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth


section
@[expose] public section
set_option autoImplicit true
set_option autoImplicit true
namespace CircuitComplexity
namespace CNF
end CNF
namespace DNF
end DNF
private lemma Literal.eval_update_ne {l : Literal N} {i : Fin N} (hne : l.var ≠ i)
    (x : BitString N) (b : Bool) :
    l.eval (Function.update x i b) = l.eval x := by
  simp only [Literal.eval]
  rw [Function.update_of_ne hne]
private lemma term_eval_update {term : List (Literal N)} {i : Fin N}
    (hmiss : ∀ l ∈ term, l.var ≠ i) (x : BitString N) (b : Bool) :
    term.all (fun l => l.eval (Function.update x i b)) = term.all (fun l => l.eval x) := by
  induction term with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.all_cons]
    rw [Literal.eval_update_ne (hmiss hd List.mem_cons_self) x b]
    rw [ih (fun l hl => hmiss l (List.mem_cons_of_mem _ hl))]
end CircuitComplexity
end
end

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit true
set_option autoImplicit true
open CircuitComplexity
namespace CircuitComplexity
namespace DNF
theorem _root_.solution (φ : DNF N)
    (f : BitString N → Bool)
    (hcomp : ∀ x, φ.eval x = f x)
    (hflip : ∀ x (i : Fin N), f (Function.update x i (!x i)) = !f x)
    (term : List (Literal N)) (hterm : term ∈ φ.terms)
    (x : BitString N) (hsat : term.all (fun l => l.eval x) = true) :
    ∀ i : Fin N, ∃ l ∈ term, l.var = i := by
  intro i
  by_contra hmiss
  push Not at hmiss
  -- hmiss : ∀ l ∈ term, l.var ≠ i
  -- Since term misses variable i, flipping i doesn't change the term
  have hsat' : term.all (fun l => l.eval (Function.update x i (!x i))) = true := by
    rw [term_eval_update hmiss]; exact hsat
  -- Both x and (flip x i) satisfy the term, so DNF is true on both
  have hx_true : φ.eval x = true := by
    simp only [DNF.eval, List.any_eq_true]
    exact ⟨term, hterm, hsat⟩
  have hx'_true : φ.eval (Function.update x i (!x i)) = true := by
    simp only [DNF.eval, List.any_eq_true]
    exact ⟨term, hterm, hsat'⟩
  -- But f flips, so f x ≠ f (flip x i)
  simp_all
end DNF
end CircuitComplexity
