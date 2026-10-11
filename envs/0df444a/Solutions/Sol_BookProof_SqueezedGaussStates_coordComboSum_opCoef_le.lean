-- Prove2me | solution 1 for BookProof.SqueezedGaussStates.coordComboSum_opCoef_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:57:57.274958+00:00
-- url     : https://prove2.me/submissions/4352b1f6-17ae-4350-afb8-5b7046e91aa9

-- Generated from ChapterSqueezedGaussStates.lean — solution of BookProof.SqueezedGaussStates.coordComboSum_opCoef_le
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
import Theorems.Thm_BookProof_SqueezedGaussStates_sqCoef_of_le
import Theorems.Thm_BookProof_SqueezedGaussStates_opCoef_of_lt
import Theorems.Thm_BookProof_SqueezedGaussStates_opCoef_top
import Theorems.Thm_BookProof_SqueezedGaussStates_Acoef_nonneg
import Theorems.Thm_BookProof_SqueezedGaussStates_Acoef_le_pow
import Theorems.Thm_BookProof_SqueezedGaussStates_Vsum_ge_one
import Theorems.Thm_BookProof_SqueezedGaussStates_Usum_le
import Theorems.Thm_BookProof_SqueezedGaussStates_coordComboSum_sqCoef
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.SqueezedGaussStates




open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (α γ v : ℝ) (M : ℕ) (hv : 4 * v ^ 2 < 1) :
    coordComboSum (opCoef α γ v M) 1 M
      ≤ ((kappa α γ v) ^ 2 / (1 - 4 * v ^ 2) + α ^ 2 * (2 * (M : ℝ) + 1) * (4 * v ^ 2) ^ M)
        * coordComboSum (sqCoef v M) 0 M := by

  have hden : 0 < 1 - 4 * v ^ 2 := by linarith
  -- rewrite the coefficient sum as an interior part plus a boundary term
  have hsplit : coordComboSum (opCoef α γ v M) 1 M
      = (∑ k ∈ Finset.range M, (kappa α γ v) ^ 2 * ((2 * (k : ℝ) + 1) * Acoef v k))
        + α ^ 2 * ((2 * (M : ℝ) + 1) * Acoef v M) := by
    rw [coordComboSum, Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hkM : k < M := Finset.mem_range.mp hk
      have hfac : (((2 * k + 1).factorial : ℕ) : ℝ)
          = (2 * (k : ℝ) + 1) * (((2 * k).factorial : ℕ) : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [opCoef_of_lt α γ v hkM, sqCoef_of_le (le_of_lt hkM), hfac, Acoef]
      ring
    · have hfac : (((2 * M + 1).factorial : ℕ) : ℝ)
          = (2 * (M : ℝ) + 1) * (((2 * M).factorial : ℕ) : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [opCoef_top, sqCoef_of_le (le_refl M), hfac, Acoef]
      ring
  have hinterior : (∑ k ∈ Finset.range M, (2 * (k : ℝ) + 1) * Acoef v k) ≤ Usum v M := by
    rw [Usum, Finset.sum_range_succ]
    have := Acoef_nonneg v M
    nlinarith [this]
  have hUsum : Usum v M ≤ Vsum v M / (1 - 4 * v ^ 2) := by
    rw [le_div_iff₀ hden]
    have := Usum_le v M
    linarith
  have hAM : Acoef v M ≤ (4 * v ^ 2) ^ M := Acoef_le_pow v M
  have hV1 : (1 : ℝ) ≤ Vsum v M := Vsum_ge_one v M
  have hk2 : 0 ≤ (kappa α γ v) ^ 2 := sq_nonneg _
  have ha2 : 0 ≤ α ^ 2 := sq_nonneg _
  have hMpos : 0 ≤ 2 * (M : ℝ) + 1 := by positivity
  rw [hsplit, coordComboSum_sqCoef]
  have hfirst : (∑ k ∈ Finset.range M, (kappa α γ v) ^ 2 * ((2 * (k : ℝ) + 1) * Acoef v k))
      ≤ (kappa α γ v) ^ 2 / (1 - 4 * v ^ 2) * Vsum v M := by
    rw [← Finset.mul_sum]
    have : (∑ k ∈ Finset.range M, (2 * (k : ℝ) + 1) * Acoef v k) ≤ Vsum v M / (1 - 4 * v ^ 2) :=
      le_trans hinterior hUsum
    calc (kappa α γ v) ^ 2 * (∑ k ∈ Finset.range M, (2 * (k : ℝ) + 1) * Acoef v k)
        ≤ (kappa α γ v) ^ 2 * (Vsum v M / (1 - 4 * v ^ 2)) := by
          exact mul_le_mul_of_nonneg_left this hk2
      _ = (kappa α γ v) ^ 2 / (1 - 4 * v ^ 2) * Vsum v M := by ring
  have hsecond : α ^ 2 * ((2 * (M : ℝ) + 1) * Acoef v M)
      ≤ α ^ 2 * (2 * (M : ℝ) + 1) * (4 * v ^ 2) ^ M * Vsum v M := by
    have hb0 : (0 : ℝ) ≤ α ^ 2 * (2 * (M : ℝ) + 1) * (4 * v ^ 2) ^ M := by positivity
    calc α ^ 2 * ((2 * (M : ℝ) + 1) * Acoef v M)
        ≤ α ^ 2 * ((2 * (M : ℝ) + 1) * (4 * v ^ 2) ^ M) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAM hMpos) ha2
      _ = (α ^ 2 * (2 * (M : ℝ) + 1) * (4 * v ^ 2) ^ M) * 1 := by ring
      _ ≤ (α ^ 2 * (2 * (M : ℝ) + 1) * (4 * v ^ 2) ^ M) * Vsum v M :=
          mul_le_mul_of_nonneg_left hV1 hb0
  linarith [hfirst, hsecond]
