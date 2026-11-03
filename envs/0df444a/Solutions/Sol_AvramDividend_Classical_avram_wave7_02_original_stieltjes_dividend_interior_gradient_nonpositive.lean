-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_stieltjes_dividend_interior_gradient_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:20:14.548106+00:00
-- url     : https://prove2.me/submissions/6616344c-85ff-4660-9a45-efb344fe533f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original Stieltjes dividend-gradient integral has its HJB sign on a
measurable strict interior region, including diffuse and singular payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (ω : Ω) (A : Set ℝ) (hA : MeasurableSet A)
    (hregion : ∀ t ∈ A,
      0 < riskProcess X x D t.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D t.toNNReal ω) < C)
    (hInt : IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      A (dividendMeasure D ω)) :
    (∫ t in A, Real.exp (-(q * t)) *
      (1 - deriv w (riskProcess X x D t.toNNReal ω))
      ∂(dividendMeasure D ω)) ≤ 0 := by
  apply MeasureTheory.integral_nonpos_of_ae
  filter_upwards [MeasureTheory.ae_restrict_mem hA] with t ht
  obtain ⟨hpos, hcap⟩ := hregion t ht
  have hSlope := hw_grad (riskProcess X x D t.toNNReal ω) hpos hcap
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _))
    (sub_nonpos.mpr hSlope)
