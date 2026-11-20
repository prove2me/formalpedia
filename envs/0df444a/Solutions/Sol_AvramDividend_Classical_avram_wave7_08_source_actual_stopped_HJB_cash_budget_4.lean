-- Prove2me | solution 4 for AvramDividend.Classical.avram_wave7_08_source_actual_stopped_HJB_cash_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:37:01.58218+00:00
-- url     : https://prove2.me/submissions/b83cc0e9-5e79-499a-a2f8-c1ce4a288920
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
import Theorems.Thm_AvramDividend_Classical_avram_integration_p4_original_stopped_source_components_public
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_p4f_drop_nonintegrable_signed_control_ae
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_three_source_martingales
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_stopped_cash_from_measurable_ito_data
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
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
    (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  classical
  have hDstrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hRuinMeas := AvramDividend.Classical.ruinTime_measurable X x D hDstrat
  have hRuinStop :=
    AvramDividend.Classical.ruinTime_stopping_rightCont_filtration X x D hDstrat
  obtain ⟨τ, hτeq, hτmeas, hτstop⟩ :=
    AvramDividend.Classical.avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
      X x D n hRuinMeas hRuinStop
  obtain ⟨W, Cash, Term, hW, hCash, hTerm, hTermMeas, hCashI⟩ :=
    AvramDividend.Classical.avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
      X x C D hD w hw_cont hw_neg q n τ hτeq hτmeas hτstop
  obtain ⟨Mc, Ms, Ml, G, R, hMcI, hMsI, hMlI, hGI,
    hMc0, hMs0, hMl0, hG, hR, hIto⟩ :=
    AvramDividend.Classical.avram_integration_p4_original_stopped_source_components_public
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop
      W Cash Term hW hCash hTerm hTermMeas hCashI
  have hNoR :=
    AvramDividend.Classical.avram_p4_d_dividend_p4f_drop_nonintegrable_signed_control_ae
      X x q w D τ W Cash Term hW hCash hTerm
      Mc Ms Ml G R hR hIto
  have hzeroI : Integrable (fun _ : Ω => (0 : ℝ)) P := by simp
  have hres : ∀ᵐ ω ∂P, G ω + (0 : ℝ) ≤ 0 := by
    filter_upwards [hG] with ω hω
    simpa using hω
  have hIto' : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + (0 : ℝ) := by
    filter_upwards [hNoR] with ω hω
    simpa using hω
  obtain ⟨M, G', H', hMI, hGI', hHI', hM0, hGH, hUpper⟩ :=
    AvramDividend.Classical.avram_p4_f_assembly_three_source_martingales
      w x Term Cash Mc Ms Ml G (fun _ => 0)
      hMcI hMsI hMlI hGI hzeroI
      hMc0 hMs0 hMl0 hres hIto'
  exact AvramDividend.Classical.avram_wave7_08_actual_stopped_cash_from_measurable_ito_data
    X hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hx hxc D hD n hn τ hτeq hτmeas hτstop
    W Cash Term M G' H' hW hCash hTerm hTermMeas
    hMI hGI' hHI' hM0 hGH hUpper
