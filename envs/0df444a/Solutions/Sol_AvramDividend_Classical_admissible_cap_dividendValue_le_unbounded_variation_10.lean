-- Prove2me | solution 10 for AvramDividend.Classical.admissible_cap_dividendValue_le_unbounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:04:08.52548+00:00
-- url     : https://prove2.me/submissions/73fdf14a-864d-429d-bdac-ce89e624c634
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_ubv_original_zero_start_dividendValue_upper
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
import Theorems.Thm_AvramDividend_Classical_avram_integration_p4_original_stopped_source_components_public
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_p4f_drop_nonintegrable_signed_control_ae
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_three_source_martingales
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_stopped_cash_from_measurable_ito_data
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_truncated_cash_le_actual_stopped_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_zero_bounded_clock_exact_stieltjes_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_ruin_clock_uniform_nat_budget_to_value
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Direct one-open-source UBV dividend-value route via actual finite stopped
    clock witnesses, retaining original ruin, cap, and time-zero payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hSmoothBoth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :=
    ⟨fun _ => hw_smooth, fun h => False.elim (hBV h)⟩
  obtain ⟨hGen, hGrad, hNonneg, hJump⟩ :=
    local_verification_stochastic_core_side_conditions
      X q w C hw_cont hw0 hSmoothBoth hw_hjb x hxc D hD
  rcases eq_or_lt_of_le hx with hzero | hxpos
  · subst x
    exact avram_wave6_10_ubv_original_zero_start_dividendValue_upper
      X hBV q w C hw0 hw_cont hw_smooth hGrad D hD hJump
  have hRuinMeas : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hD.1.1
  have hRuinStop : IsStoppingTime 𝓕.rightCont (ruinTime X x D) :=
    ruinTime_stopping_rightCont_filtration X x D hD.1.1
  have hTruncated : ∀ N : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (N : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
    intro N
    apply avram_wave7_11_original_ruin_clock_uniform_nat_budget_to_value
      X x D hD.1.1 q (N : ℝ) (ENNReal.ofReal (w x))
    intro n
    by_cases hn : n = 0
    · subst n
      simpa only [Nat.cast_zero] using
        (avram_wave7_08_zero_bounded_clock_exact_stieltjes_budget
          X q x w C hw0 hw_cont hw_smooth hGrad D hD hxc hJump
          (N : ℝ) (Nat.cast_nonneg N))
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨τ, hτeq, hτmeas, hτstop⟩ :=
      avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
        X x D n hRuinMeas hRuinStop
    obtain ⟨W, Cash, Term, hW, hCash, hTerm, hTermMeas, hCashI⟩ :=
      avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
        X x C D hD w hw_cont hw_neg q n τ hτeq hτmeas hτstop
    obtain ⟨Mc, Ms, Ml, G, R, hMcI, hMsI, hMlI, hGI,
        hMc0, hMs0, hMl0, hGnonpos, hRnonpos, hIto⟩ :=
      avram_integration_p4_original_stopped_source_components_public
        X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
        hGen hGrad x hxpos hxc D hD hNonneg hJump
        n hnpos τ hτeq hτmeas hτstop W Cash Term
        hW hCash hTerm hTermMeas hCashI
    have hDrop : ∀ᵐ ω ∂P,
        Term ω + Cash ω ≤ w x + Mc ω + Ms ω + Ml ω + G ω :=
      avram_p4_d_dividend_p4f_drop_nonintegrable_signed_control_ae
        X x q w D τ W Cash Term hW hCash hTerm
        Mc Ms Ml G R hRnonpos hIto
    have hJointNonpos : ∀ᵐ ω ∂P, G ω + (0 : ℝ) ≤ 0 := by
      simpa using hGnonpos
    have hJointUpper : ∀ᵐ ω ∂P,
        Term ω + Cash ω ≤
          w x + Mc ω + Ms ω + Ml ω + G ω + (0 : ℝ) := by
      simpa using hDrop
    obtain ⟨M, G', H', hMI, hGI', hHI', hMzero, hGH, hUpper⟩ :=
      avram_p4_f_assembly_three_source_martingales
        w x Term Cash Mc Ms Ml G (fun _ => 0)
        hMcI hMsI hMlI hGI (integrable_zero _ _ _)
        hMc0 hMs0 hMl0 hJointNonpos hJointUpper
    have hActual :
        (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) :=
      avram_wave7_08_actual_stopped_cash_from_measurable_ito_data
        X hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
        hGen hGrad x hxpos hxc D hD n hnpos τ hτeq hτmeas hτstop
        W Cash Term M G' H' hW hCash hTerm hTermMeas
        hMI hGI' hHI' hMzero hGH hUpper
    exact (avram_wave7_08_truncated_cash_le_actual_stopped_clock
      X q x D n hnpos (N : ℝ)).trans hActual
  exact dividendValue_le_of_uniform_truncated_bounds
    X q x D hD.1 (ENNReal.ofReal (w x)) hTruncated


