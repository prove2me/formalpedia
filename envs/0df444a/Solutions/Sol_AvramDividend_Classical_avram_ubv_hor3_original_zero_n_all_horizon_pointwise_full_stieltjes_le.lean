-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_zero_n_all_horizon_pointwise_full_stieltjes_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:59:24.440207+00:00
-- url     : https://prove2.me/submissions/d9727b66-5c6c-4532-b3e3-fe1ad123c61f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_any_stopping_clock_zero_horizon_pointwise_cash_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (ω : Ω) :
    (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (0 : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (w x) := by
  have hSet :
      paymentTimes (min (ruinTime X x D ω) (0 : ℝ≥0∞)) ∩ Iic T =
      paymentTimes (min (ruinTime X x D ω) (0 : ℝ≥0∞)) ∩ Iic (0 : ℝ) := by
    simp only [paymentTimes_min_zero_eq_singleton_zero]
    ext t
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_Iic]
    constructor
    · rintro ⟨rfl, _⟩
      exact ⟨rfl, le_rfl⟩
    · rintro ⟨rfl, _⟩
      exact ⟨rfl, hT⟩
  calc
    (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (0 : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
        (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (0 : ℝ≥0∞)) ∩ Iic (0 : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
      rw [hSet]
    _ ≤ ENNReal.ofReal (w x) :=
      avram_ubv_hor3_original_any_stopping_clock_zero_horizon_pointwise_cash_le
        X x q w C hw0 hw_cont hw_neg hw_smooth hw_grad hxc D hD hjump
        (min (ruinTime X x D ω) (0 : ℝ≥0∞)) ω
