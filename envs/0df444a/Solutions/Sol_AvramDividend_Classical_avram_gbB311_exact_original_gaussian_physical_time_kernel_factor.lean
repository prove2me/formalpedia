-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB311_exact_original_gaussian_physical_time_kernel_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:54:58.087958+00:00
-- url     : https://prove2.me/submissions/86f4906e-0fde-4372-83d7-506c83abfe8c

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_avram_gbB268_gaussian_inverse_sqrt_variance_volatility_time_factor
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

/-- The exact source Gaussian density on a physical real grid equals the elapsed-time kernel. -/
theorem solution (sigma : ℝ) (hsigma : 0 < sigma)
    (m i : ℕ) (hm : 0 < m) (t : ℝ)
    (ht : t ∈ Set.Ioo
      ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
      (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4)))) :
    (Real.sqrt (2 * Real.pi *
      (((NNReal.mk (sigma ^ 2) (sq_nonneg sigma)) *
        ((Real.toNNReal t -
          ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) : ℝ≥0) : NNReal) : ℝ))))⁻¹ =
      (1 / (sigma * Real.sqrt (2 * Real.pi))) *
        (t - (i : ℝ) * (1 / ((m : ℝ) ^ 4))) ^ (-(1 / 2 : ℝ)) := by
  let s : ℝ≥0 := (i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))
  let a : ℝ := (i : ℝ) * (1 / ((m : ℝ) ^ 4))
  have hsR : (s : ℝ) = (i : ℝ) * (1 / ((m : ℝ) ^ 4)) := by
    dsimp [s]
    norm_cast
  have hsa : (s : ℝ) = a := by simpa [a] using hsR
  have hsa0 : 0 ≤ a := by dsimp [a]; positivity
  have hta : a < t := ht.1
  have htt : 0 ≤ t := le_trans hsa0 (le_of_lt hta)
  have htn : ((Real.toNNReal t : ℝ≥0) : ℝ) = t :=
    Real.coe_toNNReal _ htt
  have hsleR : (s : ℝ) ≤ (Real.toNNReal t : ℝ) := by
    rw [hsa, htn]
    exact le_of_lt hta
  have hsle : s ≤ Real.toNNReal t := by exact_mod_cast hsleR
  have hdelta :
      (((Real.toNNReal t - s : ℝ≥0) : ℝ)) = t - a := by
    rw [NNReal.coe_sub hsle, htn, hsa]
  have hdt : 0 ≤ t - a := sub_nonneg.mpr (le_of_lt hta)
  have hVar :
      (((NNReal.mk (sigma ^ 2) (sq_nonneg sigma)) *
        (Real.toNNReal t - s : ℝ≥0) : NNReal) : ℝ) =
          sigma ^ 2 * (t - a) := by
    rw [NNReal.coe_mul, hdelta]
    rfl
  have hreal :
      (Real.sqrt (2 * Real.pi *
        (((NNReal.mk (sigma ^ 2) (sq_nonneg sigma)) *
          ((Real.toNNReal t - s : ℝ≥0) : NNReal) : ℝ))))⁻¹ =
        (Real.sqrt (2 * Real.pi * (sigma ^ 2 * (t - a))))⁻¹ := by
    exact congrArg (fun v : ℝ => (Real.sqrt (2 * Real.pi * v))⁻¹) hVar
  rw [show ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) = s from rfl]
  rw [hreal]
  rw [avram_gbB268_gaussian_inverse_sqrt_variance_volatility_time_factor
    sigma (t - a) hsigma hdt]
  have hPower : (Real.sqrt (t - a))⁻¹ =
      (t - a) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hdt]
  rw [hPower]
  simp [a, one_div, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
