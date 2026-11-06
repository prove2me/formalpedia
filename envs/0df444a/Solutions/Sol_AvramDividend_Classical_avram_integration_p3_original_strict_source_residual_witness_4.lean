-- Prove2me | solution 4 for AvramDividend.Classical.avram_integration_p3_original_strict_source_residual_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:31:15.990191+00:00
-- url     : https://prove2.me/submissions/c77ddb90-5337-4500-a261-a94553bb1d9c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_signed_fatou_grid_certificate
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_nonnegative_signed_fatou_prebudget_bridge
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Canonical original BV residual from independently proved signed grid
Fatou and the original finite stopped payoff's L1 and positivity properties. -/
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
    ∃ E : Ω → ℝ, Integrable E P ∧
      (∫ ω, E ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0) ≤ w x + E ω) := by
  let S : ℝ≥0 := ⟨T, hT⟩
  let Y : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  letI : IsProbabilityMeasure P := X.isProbability
  have hYInt : Integrable Y P :=
    avram_p3_bv_original_prebudget_L1 X hBV
      x C D hD w hw_cont hw_neg q (le_of_lt hq) T hT
  have hSpos : 0 < S := by exact_mod_cast hTpos
  have hYNonneg : 0 ≤ᵐ[P] Y := by
    filter_upwards [] with ω
    apply add_nonneg ENNReal.toReal_nonneg
    by_cases hr : (S : ℝ≥0∞) < ruinTime X x D ω
    · simp only [if_pos hr]
      exact mul_nonneg (Real.exp_nonneg _) (hw_nonneg ω S hSpos hr)
    · simp only [if_neg hr]
      exact le_refl _
  obtain ⟨F, M, B, hFMeas, hFInt, hFNonneg, hR, hBound, hFatou⟩ :=
    avram_p3_bv_original_source_signed_fatou_grid_certificate
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos
  have hExpected : (∫ ω, Y ω ∂P) ≤ w x :=
    avram_p3_2_nonnegative_signed_fatou_prebudget_bridge
      P (w x) Y F (fun n ω => M n ω + B n ω)
      hYInt hYNonneg hFMeas hFInt hFNonneg hR hBound hFatou
  refine ⟨fun ω => Y ω - w x, hYInt.sub (integrable_const (w x)), ?_, ?_⟩
  · rw [integral_sub hYInt (integrable_const (w x))]
    simpa using sub_nonpos.mpr hExpected
  · filter_upwards [] with ω
    change Y ω ≤ w x + (Y ω - w x)
    linarith
