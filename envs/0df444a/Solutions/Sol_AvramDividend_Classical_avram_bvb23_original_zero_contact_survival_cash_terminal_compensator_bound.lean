-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb23_original_zero_contact_survival_cash_terminal_compensator_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:09:33.667075+00:00
-- url     : https://prove2.me/submissions/281425c1-06f0-46ef-8698-c2201ed82484

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_contact_discounted_cash_le_full_HJB_rate
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
    (T : ℝ≥0) (hT : 0 < T)
    (hDiscount : ENNReal.ofReal q * (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ)) + ENNReal.ofReal (Real.exp (-(q * (T : ℝ)))) = 1) :
    ∀ᵐ ω ∂P,
      (T : ℝ≥0∞) < ruinTime X x D ω →
      (∀ u : ℝ≥0, u ≤ T → riskProcess X x D u ω = 0) →
      (∀ u : ℝ≥0, u ∈ Ioc (0 : ℝ≥0) T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) + ENNReal.ofReal (Real.exp (-(q * (T : ℝ)))) * ENNReal.ofReal (w 0) ≤
      ENNReal.ofReal (w 0) + ENNReal.ofReal (X.ν (Iio (0 : ℝ))).toReal * ENNReal.ofReal (w 0) * (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ))  := by
  have hBase :=
    avram_bvb22_original_zero_contact_discounted_cash_le_full_HJB_rate
      X hX hBV hFinite hDrift q hq w C hC hw_cont hw0 hw_neg
      hw_smooth hw_gen hw_grad x D hD T hT
  have hRateNonneg : 0 ≤ (X.ν (Iio (0 : ℝ))).toReal := ENNReal.toReal_nonneg
  have hRate :
      ENNReal.ofReal ((q + (X.ν (Iio (0 : ℝ))).toReal) * w 0) =
        (ENNReal.ofReal q + ENNReal.ofReal (X.ν (Iio (0 : ℝ))).toReal) *
          ENNReal.ofReal (w 0) := by
    rw [ENNReal.ofReal_mul (add_nonneg hq.le hRateNonneg),
      ENNReal.ofReal_add hq.le hRateNonneg]
  filter_upwards [hBase] with ω hω
  intro hs hz hj
  have hc := hω hs hz hj
  calc
    (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
        ENNReal.ofReal (Real.exp (-(q * (T : ℝ)))) * ENNReal.ofReal (w 0)
      ≤ ENNReal.ofReal ((q + (X.ν (Iio (0 : ℝ))).toReal) * w 0) *
          (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ)) +
          ENNReal.ofReal (Real.exp (-(q * (T : ℝ)))) * ENNReal.ofReal (w 0) :=
        add_le_add_left hc _
    _ = ((ENNReal.ofReal q + ENNReal.ofReal (X.ν (Iio (0 : ℝ))).toReal) *
            ENNReal.ofReal (w 0)) *
          (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ)) +
          ENNReal.ofReal (Real.exp (-(q * (T : ℝ)))) * ENNReal.ofReal (w 0) := by
        rw [hRate]
    _ = (ENNReal.ofReal q *
          (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ)) +
          ENNReal.ofReal (Real.exp (-(q * (T : ℝ))))) *
          ENNReal.ofReal (w 0) +
          ENNReal.ofReal (X.ν (Iio (0 : ℝ))).toReal *
          ENNReal.ofReal (w 0) *
          (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ)) := by
        ring
    _ = ENNReal.ofReal (w 0) +
          ENNReal.ofReal (X.ν (Iio (0 : ℝ))).toReal *
          ENNReal.ofReal (w 0) *
          (∫⁻ t in Ioc (0 : ℝ) (T : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ)) := by
        rw [hDiscount]
        simp
