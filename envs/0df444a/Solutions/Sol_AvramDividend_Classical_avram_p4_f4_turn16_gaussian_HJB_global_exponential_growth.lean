-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_turn16_gaussian_HJB_global_exponential_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:28:20.539186+00:00
-- url     : https://prove2.me/submissions/c1737102-9444-4b63-906c-c45f7b5697b0

import Mathlib.Tactic
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn16_scalar_ode_exponential_growth
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_ubv_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_original_hjb_gaussian_drift_le
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal


noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hCtop : C = ⊤) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, w y ≤ K * Real.exp (θ * y) := by
  have hσ : 0 < X.σ :=
    AvramDividend.Classical.avram_p4_f4_zero_levy_ubv_sigma_pos X hBV hν
  have ha : 0 < X.σ ^ 2 / 2 := by positivity
  exact AvramDividend.Classical.avram_p4_f4_turn16_scalar_ode_exponential_growth
    (X.σ ^ 2 / 2) X.c q w C ha hq hCtop hw0 hw_cont hw_neg hw_smooth
    (fun y hy hCy =>
      AvramDividend.Classical.avram_p4_f4_zero_levy_original_hjb_gaussian_drift_le
        X hν q w y (hw_gen y hy hCy))
