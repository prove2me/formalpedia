-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.compressionLengthBoundIter_le_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:09:04.96253+00:00
-- url     : https://prove2.me/submissions/6d06c4d8-e96e-4ef3-9025-3232ef2326b7

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Compression
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ElementaryBound
public import Theorems.Thm_DeciSigma1_Holes_Tail_splitPieceLengthBound_eq_affine
public import Theorems.Thm_DeciSigma1_Holes_Tail_compressionIntercept_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_coordinate
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_start
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_coordinate
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_start
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_stop
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open Arithmetic
private theorem compressionSlope_pos (k N : ℕ) {D : ℕ} (hD : 0 < D) :
    0 < compressionSlope k N D := by
  unfold compressionSlope Periodic.comparisonGap Periodic.statePeriodModulus
  have := Nat.factorial_pos N
  positivity
end DeciSigma1.Holes.Tail
end
end

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open Arithmetic
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (k N D r E : ℕ) :
    compressionLengthBoundIter k N D r E ≤
      (1 + r * compressionSlope k N D) ^ r *
        (E + r * compressionIntercept k N D r) := by
  by_cases hD : D = 0
  · subst D
    have hz (n E : ℕ) : compressionLengthBoundIter k N 0 n E = E := by
      induction n generalizing E with
      | zero => rfl
      | succ n ih =>
        simp [compressionLengthBoundIter, Periodic.pieceLengthBound,
          Periodic.fixedMargin, Periodic.comparisonGap, Periodic.boundaryMargin,
          Periodic.stateTransientLength, Periodic.statePeriodModulus, ih]
    simp [hz, compressionSlope, compressionIntercept, Periodic.fixedMargin,
      Periodic.comparisonGap, Periodic.boundaryMargin, Periodic.stateTransientLength,
      Periodic.statePeriodModulus]
  have hb := compressionSlope_pos k N (Nat.pos_of_ne_zero hD)
  let b := compressionSlope k N D
  let c := compressionIntercept k N D r
  let A := 1 + r * b
  have haux (n : ℕ) : n ≤ r → ∀ E,
      compressionLengthBoundIter k N D n E + r * c ≤ A ^ n * (E + r * c) := by
    induction n with
    | zero => intro _ E; simp [compressionLengthBoundIter]
    | succ n ih =>
      intro hn E
      have hm : compressionIntercept k N D (n + 1) ≤ c :=
        compressionIntercept_mono k N D hn
      have hA : 2 ≤ A := by dsimp [A, b]; nlinarith
      have hcoef := Nat.mul_le_mul_right E (Nat.mul_le_mul_right b hn)
      have hconst := Nat.mul_le_mul hn hm
      have hconst' := Nat.mul_le_mul_right (r * c) hA
      have hstep : E + (n + 1) *
          Periodic.pieceLengthBound N D (k * (N - 1)) (2 * (n + 1) + E) +
          r * c ≤ A * (E + r * c) := by
        rw [splitPieceLengthBound_eq_affine]
        dsimp [A, b] at *
        nlinarith
      rw [compressionLengthBoundIter]
      calc
        _ ≤ A ^ n * (E + (n + 1) *
            Periodic.pieceLengthBound N D (k * (N - 1)) (2 * (n + 1) + E) +
            r * c) := ih (by omega) _
        _ ≤ A ^ n * (A * (E + r * c)) := Nat.mul_le_mul_left _ hstep
        _ = A ^ (n + 1) * (E + r * c) := by rw [pow_succ]; ring
  exact (Nat.le_add_right _ _).trans (haux r le_rfl E)
end DeciSigma1.Holes.Tail
