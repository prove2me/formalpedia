-- Prove2me | solution 1 for GaussianMatrix.wishart_lambda_min_tail
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T08:35:01.026609+00:00
-- url     : https://prove2.me/submissions/4039b214-8f30-409b-a335-1da73c1462f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_wishart_lambda_min_cdf_density_bound
import Theorems.Thm_GaussianMatrix_tw_gamma_ratio_bound
import Theorems.Thm_GaussianMatrix_integral_power_exp_le

open MeasureTheory ProbabilityTheory
open scoped Matrix

open GaussianMatrix

theorem solution {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (t : ℝ) (ht : 0 < t) :
    (gaussianMatrix r k) {G | sMin (Matrix.of G)ᵀ ^ 2 ≤ t}
      ≤ ENNReal.ofReal ((1 / Real.Gamma ((k : ℝ) - r + 2))
          * (t * ((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)) := by
  -- constants of TW (B.5) and (B.6)
  set c5 : ℝ := 2 ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
      / (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1)) with hc5
  set c6 : ℝ := (((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)
      / (2 * Real.Gamma ((k : ℝ) - r + 1)) with hc6
  set a : ℝ := ((k : ℝ) - r - 1) / 2 with ha
  have hrk' : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have ha1 : -1 < a := by rw [ha]; linarith
  have hgN := Real.Gamma_pos_of_pos (show (0 : ℝ) < (k : ℝ) - r + 1 by linarith)
  have hc6pos : 0 ≤ c6 := by rw [hc6]; positivity
  have hD1 := wishart_lambda_min_cdf_density_bound hr hrk t ht
  have hD2 : c5 ≤ c6 := tw_gamma_ratio_bound hr hrk
  have hD3 := integral_power_exp_le ha1 ht.le
  calc (gaussianMatrix r k) {G | sMin (Matrix.of G)ᵀ ^ 2 ≤ t}
      ≤ ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal (c5 * x ^ a * Real.exp (-x / 2)) := hD1
    _ ≤ ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal c6 * ENNReal.ofReal (x ^ a * Real.exp (-x / 2)) := by
        refine setLIntegral_mono' measurableSet_Ioc fun x hx => ?_
        rw [← ENNReal.ofReal_mul hc6pos]
        apply ENNReal.ofReal_le_ofReal
        have : 0 ≤ x ^ a * Real.exp (-x / 2) :=
          mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.exp_pos _).le
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hD2 this
    _ = ENNReal.ofReal c6 * ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal (x ^ a * Real.exp (-x / 2)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c6 * ENNReal.ofReal (t ^ (a + 1) / (a + 1)) := by gcongr
    _ = ENNReal.ofReal ((1 / Real.Gamma ((k : ℝ) - r + 2))
          * (t * ((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)) := by
        rw [← ENNReal.ofReal_mul hc6pos]
        congr 1
        have hE : a + 1 = ((k : ℝ) - r + 1) / 2 := by rw [ha]; ring
        have hEpos : 0 < ((k : ℝ) - r + 1) / 2 := by linarith
        have hG2 : Real.Gamma ((k : ℝ) - r + 2) = ((k : ℝ) - r + 1) * Real.Gamma ((k : ℝ) - r + 1) := by
          rw [show (k : ℝ) - r + 2 = ((k : ℝ) - r + 1) + 1 by ring,
            Real.Gamma_add_one (by linarith)]
        have hsplit : (t * ((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)
            = t ^ (((k : ℝ) - r + 1) / 2) * (((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2) := by
          rw [show t * ((k : ℝ) + r) / 2 = t * (((k : ℝ) + r) / 2) by ring,
            Real.mul_rpow ht.le (by positivity)]
        rw [hE, hsplit, hG2, hc6]
        field_simp
