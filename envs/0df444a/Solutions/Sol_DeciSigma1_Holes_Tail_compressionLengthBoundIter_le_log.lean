-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.compressionLengthBoundIter_le_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:10:25.151604+00:00
-- url     : https://prove2.me/submissions/2131ce97-81fa-4cdd-9a27-7c9c6ba9152f

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ElementaryBound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_LevelElementaryBound
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedForm
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_add
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mul
public import Theorems.Thm_DeciSigma1_Holes_Tail_compressionLengthBoundIter_le_affine


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open Arithmetic
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (k N D r E H : ℕ)
    (hH : 1 ≤ H) (hN : N ≤ exp2 H) (hfac : N.factorial ≤ exp2 H)
    (hhead : 2 ^ (k * (N - 1)) ≤ exp2 H) (hD : D ≤ exp2 H)
    (hr : r ≤ exp2 H) (hE : E ≤ exp2 H) :
    compressionLengthBoundIter k N D r E ≤ exp2 (16 * (r + 1) * H) := by
  have hnd : N * D ≤ exp2 (2 * H) := by
    calc
      _ ≤ exp2 H * exp2 H := Nat.mul_le_mul hN hD
      _ = _ := by rw [← exp2_add]; congr 1; omega
  have hdf : D * N.factorial ≤ exp2 (2 * H) := by
    calc
      _ ≤ exp2 H * exp2 H := Nat.mul_le_mul hD hfac
      _ = _ := by rw [← exp2_add]; congr 1; omega
  have hmarg : Periodic.fixedMargin N D + Periodic.statePeriodModulus N D ≤
      exp2 (6 * H) := by
    calc
      _ ≤ exp2 (2 * H + 4) := by
        unfold Periodic.fixedMargin Periodic.boundaryMargin Periodic.stateTransientLength
          Periodic.statePeriodModulus
        rw [exp2_add]
        change _ ≤ exp2 (2 * H) * 16
        omega
      _ ≤ _ := exp2_mono (by omega)
  have hgap : Periodic.comparisonGap N D + Periodic.statePeriodModulus N D ≤
      exp2 (5 * H) := by
    calc
      _ ≤ exp2 (2 * H + 3) := by
        unfold Periodic.comparisonGap Periodic.boundaryMargin Periodic.stateTransientLength
          Periodic.statePeriodModulus
        rw [exp2_add]
        change _ ≤ exp2 (2 * H) * 8
        omega
      _ ≤ _ := exp2_mono (by omega)
  have hslope : compressionSlope k N D ≤ exp2 (6 * H) := by
    calc
      _ ≤ exp2 H * exp2 (5 * H) := Nat.mul_le_mul hhead hgap
      _ = _ := by rw [← exp2_add]; congr 1; omega
  have htwo : 2 * r + 1 ≤ exp2 (3 * H) := by
    have hpos : 1 ≤ exp2 H := Nat.two_pow_pos H
    calc
      _ ≤ exp2 (H + 2) := by
        rw [exp2_add]
        change _ ≤ exp2 H * 4
        omega
      _ ≤ _ := exp2_mono (by omega)
  have hinter : compressionIntercept k N D r ≤ exp2 (10 * H) := by
    have hi : compressionIntercept k N D r ≤
        (Periodic.fixedMargin N D + Periodic.statePeriodModulus N D) +
          (2 * r + 1) * compressionSlope k N D := by
      unfold compressionIntercept compressionSlope
      calc
        _ ≤ _ + ((2 * r + 1) * 2 ^ (k * (N - 1))) *
            (Periodic.comparisonGap N D + Periodic.statePeriodModulus N D) :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le _ 1)) _
        _ = _ := by ring
    have hprod : (2 * r + 1) * compressionSlope k N D ≤ exp2 (9 * H) := by
      calc
        _ ≤ exp2 (3 * H) * exp2 (6 * H) := Nat.mul_le_mul htwo hslope
        _ = _ := by rw [← exp2_add]; congr 1; omega
    have hsmall : exp2 (6 * H) ≤ exp2 (9 * H) := exp2_mono (by omega)
    calc
      _ ≤ exp2 (9 * H + 1) := by
        rw [exp2_add]
        change _ ≤ exp2 (9 * H) * 2
        omega
      _ ≤ _ := exp2_mono (by omega)
  have hbase : 1 + r * compressionSlope k N D ≤ exp2 (8 * H) := by
    have hprod : r * compressionSlope k N D ≤ exp2 (7 * H) := by
      calc
        _ ≤ exp2 H * exp2 (6 * H) := Nat.mul_le_mul hr hslope
        _ = _ := by rw [← exp2_add]; congr 1; omega
    have hpos : 1 ≤ exp2 (7 * H) := Nat.two_pow_pos _
    calc
      _ ≤ exp2 (7 * H + 1) := by
        rw [exp2_add]
        change _ ≤ exp2 (7 * H) * 2
        omega
      _ ≤ _ := exp2_mono (by omega)
  have hinit : E + r * compressionIntercept k N D r ≤ exp2 (12 * H) := by
    have hprod : r * compressionIntercept k N D r ≤ exp2 (11 * H) := by
      calc
        _ ≤ exp2 H * exp2 (10 * H) := Nat.mul_le_mul hr hinter
        _ = _ := by rw [← exp2_add]; congr 1; omega
    have hsmall : exp2 H ≤ exp2 (11 * H) := exp2_mono (by omega)
    calc
      _ ≤ exp2 (11 * H + 1) := by
        rw [exp2_add]
        change _ ≤ exp2 (11 * H) * 2
        omega
      _ ≤ _ := exp2_mono (by omega)
  calc
    _ ≤ (1 + r * compressionSlope k N D) ^ r *
        (E + r * compressionIntercept k N D r) :=
      compressionLengthBoundIter_le_affine k N D r E
    _ ≤ exp2 (8 * H) ^ r * exp2 (12 * H) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hbase r) hinit
    _ = exp2 (8 * H * r + 12 * H) := by rw [← exp2_mul, ← exp2_add]
    _ ≤ _ := exp2_mono (by nlinarith)
end DeciSigma1.Holes.Tail
