-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_caplinear_closed_horizon_all_mass_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:43:48.026108+00:00
-- url     : https://prove2.me/submissions/8cedc3d2-7eaf-4d82-b71d-34d5d61b2c44

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (y : ℝ)
    (hyD : rightLimit D T ω ≤ y) :
    (∫⁻ t in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (
      (if y ≤ c then w y else w c + (y - c)) -
      (if y - rightLimit D T ω ≤ c
        then w (y - rightLimit D T ω)
        else w c + ((y - rightLimit D T ω) - c))) := by
  have hDnonneg : 0 ≤ D T ω := by
    have hm := hD.2.1 ω (show (0 : ℝ≥0) ≤ T from zero_le)
    simpa only [hD.1 ω] using hm
  have hLnonneg : 0 ≤ rightLimit D T ω := le_trans hDnonneg
    (dividendStrategy_le_rightLimit D hD ω T)
  have hab : y - rightLimit D T ω ≤ y := by linarith
  have hsec := avram_wave4_04_cap_linear_extension_full_secant
    c hc w hw_cont hw_smooth hw_grad
    (y - rightLimit D T ω) y (sub_nonneg.mpr hyD) hab
  have hdrop : rightLimit D T ω ≤
      (if y ≤ c then w y else w c + (y - c)) -
      (if y - rightLimit D T ω ≤ c
        then w (y - rightLimit D T ω)
        else w c + ((y - rightLimit D T ω) - c)) := by
    linarith only [hsec]
  exact (avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
    q hq D hD ω T).trans (ENNReal.ofReal_le_ofReal hdrop)
