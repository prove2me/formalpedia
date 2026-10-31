-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_frozen_reserve_closed_discounted_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:26:48.928108+00:00
-- url     : https://prove2.me/submissions/d2393e8f-9482-4dff-b986-b78b4901a916

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The genuine discounted Stieltjes dividend mass through the terminal right
payment is bounded by the frozen-reserve HJB potential drop. All diffuse and
atomic payment mass is included by the actual `dividendMeasure`. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (C : ℝ≥0∞) (hC : 0 < C) (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (y : ℝ)
    (hyD : rightLimit D T ω ≤ y) (hyC : ENNReal.ofReal y ≤ C) :
    (∫⁻ t in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (w y - w (y - rightLimit D T ω)) := by
  have hDnonneg : 0 ≤ D T ω := by
    have hm := hD.2.1 ω (show (0 : ℝ≥0) ≤ T from zero_le)
    simpa only [hD.1 ω] using hm
  have hLnonneg : 0 ≤ rightLimit D T ω := le_trans hDnonneg
    (dividendStrategy_le_rightLimit D hD ω T)
  have hab : y - rightLimit D T ω ≤ y := by linarith
  have hsec := avram_wave3_03_bv_full_cap_gradient_secant
    C hC w hw_cont hw_smooth hw_grad (y - rightLimit D T ω) y
    (sub_nonneg.mpr hyD) hab hyC
  have hdrop : rightLimit D T ω ≤ w y - w (y - rightLimit D T ω) := by
    linarith only [hsec]
  exact (avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
    q hq D hD ω T).trans (ENNReal.ofReal_le_ofReal hdrop)
