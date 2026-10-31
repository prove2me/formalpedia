-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_frozen_reserve_discounted_stieltjes_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:08:23.496866+00:00
-- url     : https://prove2.me/submissions/dc2bc9b5-cf33-42d2-b7e4-a7067bf941e9

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_lintegral_le_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (C : ℝ≥0∞) (hC : 0 < C) (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (y : ℝ)
    (hyD : D T ω ≤ y) (hyC : ENNReal.ofReal y ≤ C) :
    (∫⁻ t in Ico (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (w y - w (y - D T ω)) := by
  have hDnonneg : 0 ≤ D T ω := by
    have hm := hD.2.1 ω (show (0 : ℝ≥0) ≤ T from zero_le)
    simpa only [hD.1 ω] using hm
  have hab : y - D T ω ≤ y := by linarith
  have hsec := avram_wave3_03_bv_full_cap_gradient_secant
    C hC w hw_cont hw_smooth hw_grad (y - D T ω) y
    (sub_nonneg.mpr hyD) hab hyC
  have hdrop : D T ω ≤ w y - w (y - D T ω) := by
    linarith only [hsec]
  calc
    _ ≤ dividendMeasure D ω (Ico (0 : ℝ) (T : ℝ)) :=
      discounted_stieltjes_lintegral_le_measure q hq
        (dividendMeasure D ω) (Ico (0 : ℝ) (T : ℝ))
        measurableSet_Ico (by intro t ht; exact ht.1)
    _ = ENNReal.ofReal (D T ω) :=
      dividendMeasure_Ico_zero_eq_dividendValue D hD ω T
    _ ≤ _ := ENNReal.ofReal_le_ofReal hdrop
