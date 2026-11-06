-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_zero_ruin_bounded_horizon_masked_natural_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:21:15.475821+00:00
-- url     : https://prove2.me/submissions/eba75817-fef6-4abc-9f74-957875ae81d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_ruin_bounded_horizon_masked_full_cash_budget
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
    (T : ℝ) (hT : 0 ≤ T)
    (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, if (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal = 0 then
      (∫⁻ s in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
    (∫⁻ ω, if (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal = 0 then
      ENNReal.ofReal (w x) else 0 ∂P) := by
  have hDS : IsDividendStrategy 𝓕 D := hD.1.1
  have hRuinMeas : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hDS
  have hRuinStop : IsStoppingTime 𝓕.rightCont (ruinTime X x D) :=
    ruinTime_stopping_rightCont_filtration X x D hDS
  obtain ⟨τ, hτEq, hτMeas, hτStop⟩ :=
    avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
      X x D n hRuinMeas hRuinStop
  obtain ⟨W, Cash, Term, hW, hCash, hTerm, hTermMeas, hCashI⟩ :=
    avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
      X x C D hD w hw_cont hw_neg q n τ hτEq hτMeas hτStop
  have hMasked :=
    avram_ubv_hor3_original_zero_ruin_bounded_horizon_masked_full_cash_budget
      X x q w C hw0 hw_cont hw_neg hw_smooth hw_grad hxc
      D hD hjump T hT n hn τ hτEq W Cash Term hW hCash hTerm
  simpa only [hτEq] using hMasked
