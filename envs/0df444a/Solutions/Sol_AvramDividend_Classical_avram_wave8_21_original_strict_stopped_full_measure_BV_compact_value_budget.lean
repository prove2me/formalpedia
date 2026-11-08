-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_21_original_strict_stopped_full_measure_BV_compact_value_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:46:38.926032+00:00
-- url     : https://prove2.me/submissions/b7cfc6d9-5448-41bf-9629-9edaed1cf9ed

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_compact_stopped_full_right_dividend_C1_pathwise_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_strict_survival_full_paid_measure_eq_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbC : ENNReal.ofReal b ≤ C)
    (hL1 : 1 ≤ L)
    (hLip : ∀ y ∈ Icc a b, ∀ z ∈ Icc a b,
      |w y - w z| ≤ L * |y - z|) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0),
      (T : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ rightLimit D T ω →
      x + X.X 0 ω - rightLimit D 0 ω ∈ Icc a b →
      x + X.X T ω - rightLimit D T ω ∈ Icc a b →
      ((dividendMeasure D ω)
        (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ))).toReal +
        (w (x + X.X T ω - rightLimit D T ω) -
          w (x + X.X 0 ω - rightLimit D 0 ω)) ≤
        L * (((T : ℝ) - (0 : ℝ)) * X.drift) +
          rightLimit D 0 ω := by
  filter_upwards
    [avram_wave7_02_original_BV_compact_stopped_full_right_dividend_C1_pathwise_budget
      X hX hBV x D hD C hC w hw_cont hw_smooth hw_grad
      a b L ha hab hbC hL1 hLip] with ω hω
  intro T hstrict hright hzero hterminal
  have hzt : (0 : ℝ≥0) ≤ T := zero_le
  have hpath := hω 0 T hzt hzero hterminal
  have hcash :=
    avram_wave8_21_original_strict_survival_full_paid_measure_eq_rightLimit
      X x D hD ω T hstrict
  have hcash_real :
      ((dividendMeasure D ω)
        (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ))).toReal =
          rightLimit D T ω := by
    rw [hcash, ENNReal.toReal_ofReal hright]
  rw [hcash_real]
  norm_num at hpath ⊢
  linarith
