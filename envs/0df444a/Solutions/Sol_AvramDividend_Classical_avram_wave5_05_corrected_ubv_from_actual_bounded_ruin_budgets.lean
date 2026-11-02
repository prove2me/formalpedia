-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_corrected_ubv_from_actual_bounded_ruin_budgets
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:57:36.972518+00:00
-- url     : https://prove2.me/submissions/9c48b129-532b-451a-ab13-f60428e53304

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_corrected_ubv_from_uniform_stopped_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_genuine_ruin_bounded_monotone_measurable_clocks

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Conditional corrected UBV reduction using the explicit genuine ruin clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hDiv : IsDividendStrategy 𝓕 D := by
    first
    | exact hD.1
    | exact hD.1.1
    | exact hD.1.1.1
  let τ : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    min (ruinTime X x D ω) (n : ℝ≥0∞)
  obtain ⟨hτmeas, hτmono, hτsup⟩ :=
    avram_wave5_05_genuine_ruin_bounded_monotone_measurable_clocks X x D hDiv
  apply avram_wave5_05_corrected_ubv_from_uniform_stopped_budget
    X hX hBV q hq w C hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hxc D hD hw_nonneg hjump T hT τ hτmeas hτmono hτsup
  simpa only [τ] using hBudget
