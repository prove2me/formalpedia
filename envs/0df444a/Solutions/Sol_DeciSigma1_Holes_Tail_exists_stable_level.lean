-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_stable_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:01:38.674939+00:00
-- url     : https://prove2.me/submissions/c5ac380d-b4b5-481b-ab9b-18a8ddf4618e

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
public import Theorems.Thm_DeciSigma1_Holes_Tail_coordinateCover_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_levelCoverProperty_succ
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_const_triple
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
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
variable {σ : ℕ} [DecidableEq α] [Fintype S]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (C : LevelBounds σ k (Fintype.card S)) (M : StructuralReader α S k)
    (W : Fin k → List α) (hE : ∀ i, M.Eligible W i) :
    ∃ l, 2 ≤ l ∧ l ≤ levelCount k ∧
        ∀ i, (CoordinateCover C (l - 1) M W i ↔ CoordinateCover C l M W i) ∧
      (LevelCoverProperty C (l - 2) M W i ↔ LevelCoverProperty C (l - 1) M W i) := by
  let P : Fin k ⊕ Fin k → ℕ → Prop := fun x l => match x with
    | .inl i => CoordinateCover C l M W i
    | .inr i => LevelCoverProperty C l M W i
  have hmono : ∀ x l, P x l → P x (l + 1) := by
    intro x l hx
    cases x with
    | inl i => exact coordinateCover_mono C (Nat.le_succ l) hx
    | inr i => exact levelCoverProperty_succ C (hE i) hx
  obtain ⟨j, hj, hjP⟩ := exists_const_triple P hmono
  have hcard : Fintype.card (Fin k ⊕ Fin k) = 2 * k := by simp; ring
  rw [hcard] at hj
  refine ⟨3 * j + 2, by omega, by unfold levelCount; omega, fun i => ⟨?_, ?_⟩⟩
  · have h := hjP (.inl i)
    simp only [P] at h
    rw [show 3 * j + 2 - 1 = 3 * j + 1 by omega]
    exact ⟨fun h1 => coordinateCover_mono C (Nat.le_succ _) h1,
      fun h2 => coordinateCover_mono C (Nat.le_succ _) (h.mpr h2)⟩
  · have h := hjP (.inr i)
    simp only [P] at h
    rw [show 3 * j + 2 - 2 = 3 * j by omega, show 3 * j + 2 - 1 = 3 * j + 1 by omega]
    exact ⟨fun h1 => levelCoverProperty_succ C (hE i) h1,
      fun h2 => h.mpr (levelCoverProperty_succ C (hE i) h2)⟩
end DeciSigma1.Holes.Tail
