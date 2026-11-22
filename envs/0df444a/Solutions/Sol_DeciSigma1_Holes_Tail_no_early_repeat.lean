-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.no_early_repeat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:54:23.557913+00:00
-- url     : https://prove2.me/submissions/b9ef2bb9-03ae-45f3-9592-dfe866529504

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_spec
public import Theorems.Thm_DeciSigma1_Readers_Table_runPrefix_add
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable {M : StructuralReader α S k} {W : Fin k → List α} {i : Fin k}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (h : M.Eligible W i) {a' a : ℕ} (ha : a' < a)
    (haJ : a ≤ M.firstRejection W i)
    (htext : ∀ t, t < M.firstRejection W i - a → (W i)[a' + t]? = (W i)[a + t]?)
    (hq : M.runPrefix W i a' = M.runPrefix W i a) : False := by
  obtain ⟨hJl, hJr, hJb⟩ := StructuralReader.firstRejection_spec h
  set J := M.firstRejection W i
  have htake : ((W i).drop a').take (J - a) = ((W i).drop a).take (J - a) := by
    apply List.ext_getElem?
    intro t
    by_cases ht : t < J - a
    · rw [List.getElem?_take_of_lt ht, List.getElem?_take_of_lt ht, List.getElem?_drop,
        List.getElem?_drop]
      exact htext t ht
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have h1 : M.runPrefix W i (a' + (J - a)) = M.runPrefix W i J := by
    rw [Table.runPrefix_add, hq, htake, ← Table.runPrefix_add, show a + (J - a) = J by omega]
  have h2 := hJb (a' + (J - a)) (by omega)
  rw [h1, hJr] at h2
  exact absurd h2 (by decide)
end DeciSigma1.Holes.Tail
