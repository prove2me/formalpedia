-- Prove2me | solution 6 for AvramDividend.Classical.avram_p3_bv_original_positive_horizon_stopped_prebudget_HJB
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:32:55.233491+00:00
-- url     : https://prove2.me/submissions/6df91081-5c52-475a-8ffc-d89acf0c7e04
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_integration_p3_original_strict_source_residual_witness
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Canonical P3 prebudget, conditional only on the independent original source residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by
  let S : ℝ≥0 := ⟨T, hT⟩
  let pay : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0)
  obtain ⟨E, hEint, hEmean, hEpath⟩ :=
    avram_integration_p3_original_strict_source_residual_witness
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos
  letI : IsProbabilityMeasure P := X.isProbability
  have hPayInt : Integrable pay P := by
    exact avram_p3_bv_original_prebudget_L1 X hBV
      x C D hD w hw_cont hw_neg q (le_of_lt hq) T hT
  have hUpperInt : Integrable (fun ω => w x + E ω) P :=
    (integrable_const (w x)).add hEint
  have hPath : ∀ᵐ ω ∂P, pay ω ≤ w x + E ω := by
    filter_upwards [hEpath] with ω hω
    exact hω
  have hExpected :
      (∫ ω, pay ω ∂P) ≤ ∫ ω, w x + E ω ∂P :=
    integral_mono_ae hPayInt hUpperInt hPath
  have hUpperMean :
      (∫ ω, w x + E ω ∂P) = w x + ∫ ω, E ω ∂P := by
    rw [integral_add (integrable_const (w x)) hEint]
    simp
  change (∫ ω, pay ω ∂P) ≤ w x
  calc
    _ ≤ ∫ ω, w x + E ω ∂P := hExpected
    _ = w x + ∫ ω, E ω ∂P := hUpperMean
    _ ≤ w x := by linarith only [hEmean]
