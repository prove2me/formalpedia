-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_capped_expected_terminal_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:11:56.090003+00:00
-- url     : https://prove2.me/submissions/14141371-bfb9-48d6-a753-e3a4716e271b

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_capped_terminal_hjb_budget_all_paths

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- In expectation, the stopped HJB budget pays for the actual closed
    horizon Stieltjes reward after adding the terminal verification drop. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω,
      (∫⁻ s in paymentTimes
          (min (ruinTime X x D ω) (ENNReal.ofReal (T : ℝ))),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) +
      ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) *
        (w (riskProcess X x D T ω) -
          w (riskProcess X x D T ω -
            (rightLimit D T ω - D T ω)))) ∂P) := by
  apply lintegral_mono
  intro ω
  exact local_verification_capped_terminal_hjb_budget_all_paths
    X x q w C hw_cont hw_smooth hw_hjb D hD hxc ω T hT
