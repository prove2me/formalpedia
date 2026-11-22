-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.prefix_drop_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:48:41.0178+00:00
-- url     : https://prove2.me/submissions/3e180693-97a7-42e1-aca9-3be93fbca3af

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
theorem _root_.solution {u x : List α} {a : ℕ} (ha : a ≤ x.length) :
    u <+: x.drop a ↔ a + u.length ≤ x.length ∧ ∀ j < u.length, x[a + j]? = u[j]? := by
  rw [List.prefix_iff_eq_take]
  constructor
  · intro h
    have hl : u.length ≤ (x.drop a).length := by
      rw [h]; simp only [List.length_take]; exact min_le_right _ _
    refine ⟨by simp at hl; omega, fun j hj => ?_⟩
    rw [congrArg (fun l => l[j]?) h, List.getElem?_take_of_lt hj, List.getElem?_drop]
  · rintro ⟨hl, h⟩
    apply List.ext_getElem?
    intro j
    by_cases hj : j < u.length
    · rw [List.getElem?_take_of_lt hj, List.getElem?_drop, h j hj]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
end DeciSigma1.Holes.Tail
