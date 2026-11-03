-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_21_original_stieltjes_ae_interior_discounted_diffuse_correction_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:47:02.715051+00:00
-- url     : https://prove2.me/submissions/15c28532-9240-4a4d-ac52-656dcf392403

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

/-- Original Stieltjes correction is nonpositive under its own measure-a.e. interior condition. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (A : Set ℝ) (hA : MeasurableSet A)
    (hregion : ∀ᵐ t ∂(dividendMeasure D ω).restrict A,
      0 < riskProcess X x D t.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D t.toNNReal ω) < C) :
    (∫ t in A, Real.exp (-(q * t)) *
      (1 - deriv w (riskProcess X x D t.toNNReal ω))
      ∂(dividendMeasure D ω)) ≤ 0 := by
  refine integral_nonpos_of_ae ?_
  filter_upwards [hregion] with t ht
  have hgradient : 1 ≤ deriv w (riskProcess X x D t.toNNReal ω) :=
    hw_grad (riskProcess X x D t.toNNReal ω) ht.1 ht.2
  have hcorrection : 1 - deriv w
      (riskProcess X x D t.toNNReal ω) ≤ 0 :=
    sub_nonpos.mpr hgradient
  have hdiscount : 0 ≤ Real.exp (-(q * t)) :=
    (Real.exp_pos (-(q * t))).le
  exact mul_nonpos_of_nonneg_of_nonpos hdiscount hcorrection
