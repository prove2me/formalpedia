-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb22_original_zero_contact_discounted_cash_le_full_HJB_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:16:04.548572+00:00
-- url     : https://prove2.me/submissions/e26237f6-3462-4994-981e-138423409b53

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_nojump_zero_contact_weighted_cash_prefix
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_origin_HJB_drift_ceiling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hDrift : 0 ≤ X.drift) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      (T : ℝ≥0∞) < ruinTime X x D ω →
      (∀ u : ℝ≥0, u ≤ T → riskProcess X x D u ω = 0) →
      (∀ u : ℝ≥0, u ∈ Ioc (0 : ℝ≥0) T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal ((q + (X.ν (Iio (0 : ℝ))).toReal) * w 0) *
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ))
       := by
  have hbound :=
    avram_bv_correct12_finite_activity_origin_HJB_drift_ceiling
      X hX hBV hFinite q w C hC hw_cont hw0 hw_neg
      hw_smooth hw_gen hw_grad
  have hcash :=
    avram_bv_zero13_original_nojump_zero_contact_weighted_cash_prefix
      X hBV hFinite hDrift x C D hD T hT
  filter_upwards [hcash] with ω hc
  intro hsurv hzero hnojump
  have heq := hc hsurv hzero hnojump
    (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t))))
  calc
    (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      = ∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(ENNReal.ofReal X.drift • (volume : Measure ℝ)) := heq
    _ = ENNReal.ofReal X.drift *
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ)) := by
      rw [setLIntegral_smul_measure]
      rfl
    _ ≤ ENNReal.ofReal ((q + (X.ν (Iio (0 : ℝ))).toReal) * w 0) *
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (ENNReal.ofReal_le_ofReal hbound) zero_le
