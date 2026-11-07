-- Prove2me | solution 3 for AvramDividend.Classical.avram_f12_original_infinitecap_exact_stopped_clock_localisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:17:07.591197+00:00
-- url     : https://prove2.me/submissions/b585423d-4af4-4fe5-8150-824fe98040dc

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f14_original_infinitecap_upperbarrier_localising_clocks
import Theorems.Thm_AvramDividend_Classical_avram_f15_continuous_zero_negative_uniform_bounded_above
import Theorems.Thm_AvramDividend_Classical_avram_f18_original_stopped_postpayment_reserve_upper_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_zero_negative_payoff_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_ruin_piecewise_book_postpayment_terminal_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_ordered_clocks_closed_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_discounted_terminal_integrable_of_ae_bound


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (W Cash Term : Ω → ℝ) (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) (hTermMeas : AEStronglyMeasurable Term P) (hCashI : Integrable Cash P) (hCtop : C = ⊤) :
    ∃ (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ),
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (σ k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, σ k ω ≤ τ ω) ∧
      (∀ k ω, F k ω =
        Real.exp (-(q * (σ k ω : ℝ))) *
          w (if σ k ω = 0 ∨
                (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
            else riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) ∧
      (∀ k, Measurable (F k)) ∧
      (∀ k, Integrable (F k) P) ∧
      (∀ᵐ ω ∂P, Tendsto
        (fun k => ENNReal.ofReal (F k ω)) atTop
        (𝓝 (ENNReal.ofReal (Term ω + Cash ω)))) := by
  classical
  obtain ⟨σ, hStop, hMeas, hLe, hBound, hEventually⟩ :=
    avram_f14_original_infinitecap_upperbarrier_localising_clocks
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
      hTermMeas hCashI hCtop
  let Wloc : ℕ → Ω → ℝ := fun k ω =>
    if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
    else riskProcess X x D (σ k ω) ω
  let Cloc : ℕ → Ω → ℝ := fun k ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let Tloc : ℕ → Ω → ℝ := fun k ω =>
    Real.exp (-(q * (σ k ω : ℝ))) * w (Wloc k ω)
  let F : ℕ → Ω → ℝ := fun k ω => Tloc k ω + Cloc k ω
  have hwm : Measurable w :=
    avram_p4_c_generator_zero_negative_payoff_measurable w hw_cont hw_neg
  have hCashTauI : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P := by
    have heq : Cash = (fun ω =>
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :=
      funext hCash
    rw [heq] at hCashI
    exact hCashI
  refine ⟨σ, F, hStop, hLe, ?_, ?_, ?_, ?_⟩
  · intro k ω
    rfl
  · intro k
    have hWM : Measurable (Wloc k) :=
      avram_wave6_06_original_ruin_piecewise_book_postpayment_terminal_measurable
        X x D hD.1.1 (σ k) (hStop k) (Wloc k) (by intro ω; rfl)
    have hTm : Measurable (Tloc k) := by
      have hTimeExp : Measurable
          (fun ω : Ω => Real.exp (-(q * (σ k ω : ℝ)))) :=
        Real.measurable_exp.comp ((measurable_const.mul (hMeas k)).neg)
      exact hTimeExp.mul (hwm.comp hWM)
    have hCM : Measurable (Cloc k) := by
      have hCashENN : Measurable (fun ω =>
          ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) :=
        avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
          X x D hD.1.1 q (fun ω => (σ k ω : ℝ)) (hMeas k)
      exact ENNReal.measurable_toReal.comp hCashENN
    exact hTm.add hCM
  · intro k
    obtain ⟨B, hBnn, hB⟩ :=
      avram_f15_continuous_zero_negative_uniform_bounded_above
        w hw_cont hw_neg (x + ((k : ℝ) + 1))
    have hWB : ∀ ω, |w (Wloc k ω)| ≤ B := by
      intro ω
      apply hB
      exact avram_f18_original_stopped_postpayment_reserve_upper_bound
        X x D hD.1.1 ω (σ k ω) ((k : ℝ) + 1) (hBound k ω)
    have hWM : Measurable (Wloc k) :=
      avram_wave6_06_original_ruin_piecewise_book_postpayment_terminal_measurable
        X x D hD.1.1 (σ k) (hStop k) (Wloc k) (by intro ω; rfl)
    have hTimeExp : Measurable
        (fun ω : Ω => Real.exp (-(q * (σ k ω : ℝ)))) :=
      Real.measurable_exp.comp ((measurable_const.mul (hMeas k)).neg)
    have hTM : Measurable (Tloc k) :=
      hTimeExp.mul (hwm.comp hWM)
    have hTI : Integrable (Tloc k) P :=
      avram_p4_e_localise_discounted_terminal_integrable_of_ae_bound
        X q (le_of_lt hq) (σ k) w (Wloc k)
        hTM.aestronglyMeasurable B (Filter.Eventually.of_forall hWB)
    have hCI : Integrable (Cloc k) P :=
      avram_ubv_loc6_original_ordered_clocks_closed_cash_L1
        X x q (le_of_lt hq) C D hD (σ k) τ
        (hLe k) (hMeas k) hCashTauI
    exact hTI.add hCI
  · filter_upwards [] with ω
    have he : (fun k => ENNReal.ofReal (F k ω)) =ᶠ[atTop]
        (fun _ => ENNReal.ofReal (Term ω + Cash ω)) := by
      filter_upwards [hEventually ω] with k hk
      congr 1
      change Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
        else riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal =
          Term ω + Cash ω
      rw [hk, ← hW ω, ← hTerm ω, ← hCash ω]
    exact (tendsto_congr' he).2 tendsto_const_nhds
