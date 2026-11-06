-- Prove2me | solution 4 for AvramDividend.Classical.avram_wave7_08_ubv_positive_n_positive_horizon_source_ito_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:29:41.740112+00:00
-- url     : https://prove2.me/submissions/91ee53e5-8b61-4244-b55e-1626a19d60e2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
import Theorems.Thm_AvramDividend_Classical_avram_integration_p4_original_stopped_source_components_public
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_p4f_drop_nonintegrable_signed_control_ae
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_three_source_martingales
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_stopped_cash_from_measurable_ito_data
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_truncated_cash_le_actual_stopped_clock
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
    (T : ℝ) (hT : 0 < T)
    (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
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
  obtain ⟨Mc, Ms, Ml, G, R, hMcI, hMsI, hMlI, hGI,
      hMcZero, hMsZero, hMlZero, hGNonpos, hRNonpos, hResidual⟩ :=
    avram_integration_p4_original_stopped_source_components_public
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      τ hτEq hτMeas hτStop W Cash Term hW hCash hTerm hTermMeas hCashI
  have hDrop : ∀ᵐ ω ∂P, Term ω + Cash ω ≤
      w x + Mc ω + Ms ω + Ml ω + G ω :=
    avram_p4_d_dividend_p4f_drop_nonintegrable_signed_control_ae
      X x q w D τ W Cash Term hW hCash hTerm
      Mc Ms Ml G R hRNonpos hResidual
  have hZeroI : Integrable (fun _ : Ω => (0 : ℝ)) P := by simp
  have hSign : ∀ᵐ ω ∂P, G ω + (0 : ℝ) ≤ 0 := by
    filter_upwards [hGNonpos] with ω hg
    simpa using hg
  have hWithZero : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + (0 : ℝ) := by
    filter_upwards [hDrop] with ω hi
    simpa using hi
  obtain ⟨M, G', H', hMI, hGI', hHI, hM0, hGH, hBudget⟩ :=
    avram_p4_f_assembly_three_source_martingales
      w x Term Cash Mc Ms Ml G (fun _ : Ω => (0 : ℝ))
      hMcI hMsI hMlI hGI hZeroI
      hMcZero hMsZero hMlZero hSign hWithZero
  have hNatural :=
    avram_wave7_08_actual_stopped_cash_from_measurable_ito_data
      X hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD n hn
      τ hτEq hτMeas hτStop W Cash Term M G' H'
      hW hCash hTerm hTermMeas hMI hGI' hHI hM0 hGH hBudget
  exact (avram_wave7_08_truncated_cash_le_actual_stopped_clock
    X q x D n hn T).trans hNatural
