-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.compressionLengthBoundIter_le_exp2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:10:25.753095+00:00
-- url     : https://prove2.me/submissions/18f7f9a2-1416-45ee-a69e-99124c899f44

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Compression
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ElementaryBound
public import Theorems.Thm_DeciSigma1_Holes_Tail_compressionLengthBoundIter_le_affine
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_add
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_add_le
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mul
public import Theorems.Thm_DeciSigma1_Arithmetic_factorial_le_exp2_sq
public import Theorems.Thm_DeciSigma1_Arithmetic_le_exp2
public import Theorems.Thm_DeciSigma1_Arithmetic_succ_le_exp2
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_coordinate
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_start
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
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
private theorem margins_le_exp2 (N D : ℕ) :
    Periodic.fixedMargin N D + Periodic.statePeriodModulus N D ≤
        exp2 (N * N + N + D + 4) ∧
      Periodic.comparisonGap N D + Periodic.statePeriodModulus N D ≤
        exp2 (N * N + N + D + 3) := by
  have htrans : N * D ≤ exp2 (N * N + N + D) := by
    calc
      _ ≤ exp2 N * exp2 D := Nat.mul_le_mul (le_exp2 N) (le_exp2 D)
      _ = exp2 (N + D) := (exp2_add N D).symm
      _ ≤ _ := exp2_mono (by omega)
  have hmod : D * N.factorial ≤ exp2 (N * N + N + D) := by
    calc
      _ ≤ exp2 D * exp2 (N * N) := Nat.mul_le_mul (le_exp2 D) (factorial_le_exp2_sq N)
      _ = exp2 (D + N * N) := (exp2_add D (N * N)).symm
      _ ≤ _ := exp2_mono (by omega)
  unfold Periodic.fixedMargin Periodic.comparisonGap Periodic.boundaryMargin
    Periodic.stateTransientLength Periodic.statePeriodModulus
  rw [exp2_add (N * N + N + D) 4, exp2_add (N * N + N + D) 3]
  change _ ≤ exp2 (N * N + N + D) * 16 ∧ _ ≤ exp2 (N * N + N + D) * 8
  constructor <;> nlinarith
private theorem compressionSlope_le_exp2 (k N D : ℕ) :
    compressionSlope k N D ≤ exp2 (arithmeticBudget k N D) := by
  have hQ : 2 ^ (k * (N - 1)) ≤ exp2 (k * N) :=
    exp2_mono (Nat.mul_le_mul_left k (Nat.sub_le N 1))
  calc
    _ ≤ exp2 (k * N) * exp2 (N * N + N + D + 3) :=
      Nat.mul_le_mul hQ (margins_le_exp2 N D).2
    _ = exp2 (k * N + (N * N + N + D + 3)) := (exp2_add _ _).symm
    _ ≤ _ := exp2_mono (by unfold arithmeticBudget; omega)
private theorem compressionIntercept_le_exp2 (k N D r : ℕ) :
    compressionIntercept k N D r ≤ exp2 (arithmeticBudget k N D + r + 1) := by
  let q := arithmeticBudget k N D
  have hA : Periodic.fixedMargin N D + Periodic.statePeriodModulus N D ≤ exp2 q :=
    (margins_le_exp2 N D).1.trans (exp2_mono (by dsimp [q, arithmeticBudget]; omega))
  have hb := compressionSlope_le_exp2 k N D
  have hc : compressionIntercept k N D r ≤
      (Periodic.fixedMargin N D + Periodic.statePeriodModulus N D) +
        (2 * r + 1) * compressionSlope k N D := by
    unfold compressionIntercept compressionSlope
    calc
      _ ≤ _ + ((2 * r + 1) * 2 ^ (k * (N - 1))) *
          (Periodic.comparisonGap N D + Periodic.statePeriodModulus N D) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le _ 1)) _
      _ = _ := by ring
  calc
    _ ≤ exp2 q + (2 * r + 1) * exp2 q :=
      hc.trans (Nat.add_le_add hA (Nat.mul_le_mul_left _ hb))
    _ = 2 * (r + 1) * exp2 q := by ring
    _ ≤ 2 * exp2 r * exp2 q :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (succ_le_exp2 r))
    _ = _ := by
      change exp2 1 * exp2 r * exp2 q = _
      rw [← exp2_add, ← exp2_add]
      congr 1; dsimp [q]; omega
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
      exp2 (16 * (k + N + D + r + 2) ^ 4) * (E + 1) := by
  let q := arithmeticBudget k N D
  have hb := compressionSlope_le_exp2 k N D
  have hc := compressionIntercept_le_exp2 k N D r
  have hbase : 1 + r * compressionSlope k N D ≤ exp2 (r + q + 1) := by
    calc
      _ ≤ exp2 0 + exp2 r * exp2 q :=
        Nat.add_le_add (le_refl 1) (Nat.mul_le_mul (le_exp2 r) hb)
      _ = exp2 0 + exp2 (r + q) := by rw [← exp2_add]
      _ ≤ _ := by simpa using exp2_add_le 0 (r + q)
  have hrc : r * compressionIntercept k N D r ≤ exp2 (q + 2 * r + 1) := by
    calc
      _ ≤ exp2 r * exp2 (q + r + 1) := Nat.mul_le_mul (le_exp2 r) hc
      _ = _ := by rw [← exp2_add]; congr 1; omega
  have hE : E + r * compressionIntercept k N D r ≤
      exp2 (q + 2 * r + 1) * (E + 1) := by
    have hpos : 1 ≤ exp2 (q + 2 * r + 1) := Nat.one_le_pow _ _ (by decide)
    nlinarith
  have hpoly : (r + q + 1) * r + (q + 2 * r + 1) ≤
      16 * (k + N + D + r + 2) ^ 4 := by
    dsimp [q, arithmeticBudget]
    ring_nf
    omega
  calc
    _ ≤ (1 + r * compressionSlope k N D) ^ r *
        (E + r * compressionIntercept k N D r) :=
      compressionLengthBoundIter_le_affine k N D r E
    _ ≤ exp2 (r + q + 1) ^ r * (exp2 (q + 2 * r + 1) * (E + 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hbase r) hE
    _ = exp2 ((r + q + 1) * r + (q + 2 * r + 1)) * (E + 1) := by
      rw [← exp2_mul, ← Nat.mul_assoc, ← exp2_add]
    _ ≤ _ := Nat.mul_le_mul_right _ (exp2_mono hpoly)
end DeciSigma1.Holes.Tail
