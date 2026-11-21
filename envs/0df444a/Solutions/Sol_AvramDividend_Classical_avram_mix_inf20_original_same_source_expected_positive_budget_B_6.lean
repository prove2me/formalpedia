-- Prove2me | solution 6 for AvramDividend.Classical.avram_mix_inf20_original_same_source_expected_positive_budget_B
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T19:14:48.710843+00:00
-- url     : https://prove2.me/submissions/75f878ab-dc6b-4544-b2be-fb30eb5a4c3d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_E_infinite_true_single_clock_physical_signed_reward_upper
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_positive_expected_budget_finitecap
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
import Theorems.Thm_AvramDividend_Classical_avram_gbB36_interior_cap_positive_value_from_gradient
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin24_initial_event_condcentered_mask_transfer
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
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
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ k, (∫ ω in {ω : Ω | σ k ω ≠ 0}, F k ω ∂P) ≤
      w x * (P {ω : Ω | σ k ω ≠ 0}).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  by_cases hTop : C = ⊤
  · have hτmeas : Measurable (fun ω : Ω => (τ ω : ℝ)) :=
      avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable τ hτstop
    obtain ⟨W, Cash, Term, hW, hCash, hTerm, hTermMeas, hCashI⟩ :=
      avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
        X x C D hD w hw_cont hw_neg q n τ hτeq hτmeas hτstop
    have hWitness :=
      avram_jump6_E_infinite_true_single_clock_physical_signed_reward_upper
        X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg
        hjump n hn τ hτeq hτmeas hτstop W Cash Term
        hW hCash hTerm hTermMeas hCashI σ F hσstop hσle hFsource
        hFI hTop hInfiniteActivity
    have hwx : 0 ≤ w x :=
      avram_gbB36_interior_cap_positive_value_from_gradient
        C w hw0 hw_cont hw_smooth hw_grad x (le_of_lt hx) hxc
    intro k
    obtain ⟨M, G, R, hMI, hM0, hG, hR, hUpper⟩ := hWitness k
    have hE : MeasurableSet[𝓕.rightCont 0] {ω : Ω | σ k ω ≠ 0} :=
      avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable
        (σ k) (hσstop k)
    have hUpper' : ∀ᵐ ω ∂P, F k ω ≤ w x + M ω := by
      filter_upwards [hUpper, hG, hR] with ω hu hg hr
      linarith
    have hUpperE : ∀ᵐ ω ∂(P.restrict {ω : Ω | σ k ω ≠ 0}),
        F k ω ≤ w x + M ω := ae_restrict_of_ae hUpper'
    exact avram_mix_fin24_initial_event_condcentered_mask_transfer
      (𝓕.rightCont 0) (𝓕.rightCont.le 0)
      {ω : Ω | σ k ω ≠ 0} {ω : Ω | σ k ω ≠ 0}
      hE (by intro ω h; exact h) (w x) hwx
      (F k) M (hFI k) hMI hM0 hUpperE
  · exact avram_jump6_B_original_positive_expected_budget_finitecap
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg
      hjump n hn τ hτeq hτstop σ F hσstop hσle hFsource
      hFI hInfiniteActivity hTop
