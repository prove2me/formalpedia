-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave7_08_ubv_positive_reserve_positive_horizon_source_ito_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:00:46.801333+00:00
-- url     : https://prove2.me/submissions/70e8209a-01c4-4d46-b4f0-d0ae47ff31a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_ito_residual_given_real_stopped_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_stopped_cash_from_measurable_ito_data
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_truncated_cash_le_actual_stopped_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_zero_bounded_clock_exact_stieltjes_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_ruin_clock_uniform_nat_budget_to_value

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hStrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hRuinMeas : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hStrategy
  have hRuinStop : IsStoppingTime 𝓕.rightCont (ruinTime X x D) :=
    ruinTime_stopping_rightCont_filtration X x D hStrategy
  have hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨τ, hτeq, hτmeas, hτstop⟩ :=
        avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
          X x D n hRuinMeas hRuinStop
      obtain ⟨W, Cash, Term, M, G, H, hW, hCash, hTerm,
        hTermMeas, hMI, hGI, hHI, hMzero, hGH, hUpper⟩ :=
        avram_wave7_08_source_ito_residual_given_real_stopped_clock
          X hX hBV q hq w C hC hw0 hw_cont hw_neg
          hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
          n hn τ hτeq hτmeas hτstop
      have hStopped :=
        avram_wave7_08_actual_stopped_cash_from_measurable_ito_data
          X hBV q hq w C hC hw0 hw_cont hw_neg
          hw_smooth hw_gen hw_grad x hx hxc D hD
          n hn τ hτeq hτmeas hτstop
          W Cash Term M G H hW hCash hTerm hTermMeas
          hMI hGI hHI hMzero hGH hUpper
      exact (avram_wave7_08_truncated_cash_le_actual_stopped_clock
        X q x D n hn T).trans hStopped
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      simpa only [Nat.cast_zero] using
        (avram_wave7_08_zero_bounded_clock_exact_stieltjes_budget
          X q x w C hw0 hw_cont hw_smooth hw_grad
          D hD hxc hjump T (le_of_lt hT))
  exact avram_wave7_11_original_ruin_clock_uniform_nat_budget_to_value
    X x D hStrategy q T (ENNReal.ofReal (w x)) hBudget
