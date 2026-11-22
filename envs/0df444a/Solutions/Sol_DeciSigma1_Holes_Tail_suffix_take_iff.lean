-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.suffix_take_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:48:41.553628+00:00
-- url     : https://prove2.me/submissions/4dd6a267-ce44-4fc3-9314-64b608be3a47

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {u x : List α} {e : ℕ} (he : e ≤ x.length) :
    u <:+ x.take e ↔ u.length ≤ e ∧ ∀ j < u.length, x[e - u.length + j]? = u[j]? := by
  rw [List.suffix_iff_eq_drop]
  simp only [List.length_take, min_eq_left he]
  constructor
  · intro h
    have hl : u.length ≤ e := by
      have := congrArg List.length h
      simp only [List.length_drop, List.length_take, min_eq_left he] at this
      omega
    refine ⟨hl, fun j hj => ?_⟩
    rw [congrArg (fun l => l[j]?) h, List.getElem?_drop, List.getElem?_take_of_lt (by omega)]
  · rintro ⟨hl, h⟩
    apply List.ext_getElem?
    intro j
    by_cases hj : j < u.length
    · rw [List.getElem?_drop, List.getElem?_take_of_lt (by omega), h j hj]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
end DeciSigma1.Holes.Tail
