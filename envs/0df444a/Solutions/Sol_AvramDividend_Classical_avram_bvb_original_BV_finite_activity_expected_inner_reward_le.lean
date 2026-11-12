-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_original_BV_finite_activity_expected_inner_reward_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T23:50:13.540448+00:00
-- url     : https://prove2.me/submissions/b870ea59-703d-4590-8a65-e3bf38f75d36
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_finite_original_zero_intensity_cash_reward_le
import Theorems.Thm_AvramDividend_Classical_avram_bvb_finite_original_positive_intensity_cash_reward_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

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
    (T : ℝ) (hT : 0 < T)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n : ℕ, (∫ ω, F n ω ∂P) ≤ w x := by
  classical
  by_cases hzero : X.ν (Iio (0 : ℝ)) = 0
  · exact
      AvramDividend.Classical.avram_bvb_finite_original_zero_intensity_cash_reward_le
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad x hx hxc
        D hD hw_nonneg hjump T hT hFinite hzero
  · have hpositive : 0 < X.ν (Iio (0 : ℝ)) := by
      have hnonneg : (0 : ℝ≥0∞) ≤ X.ν (Iio (0 : ℝ)) := bot_le
      exact lt_of_le_of_ne hnonneg (Ne.symm hzero)
    exact
      AvramDividend.Classical.avram_bvb_finite_original_positive_intensity_cash_reward_le
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad x hx hxc
        D hD hw_nonneg hjump T hT hFinite hpositive
