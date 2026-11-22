-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_finiteactivity_anycap_canonical_true_stopped_reward_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T19:57:04.66847+00:00
-- url     : https://prove2.me/submissions/8f8af8f3-cfeb-406d-92ae-4f926b1f5710

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_canonical_true_stopped_reward_measurable_Cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_jump6_finitecap_activity_root_budget_source_preflight
import Theorems.Thm_AvramDividend_Classical_avram_jump6_finiteactivity_topcap_HJB_actual_stopped_full_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original HJB all-cap actual stopped reward L1, no cash or terminal
measurability hypothesis, leaving only the expected Ito source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxpos : 0 < x)
    (k : ℕ) (hk : 0 < k)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
 :
    AEStronglyMeasurable Term P ∧
    Integrable Cash P ∧
    Integrable Term P ∧
    Integrable (fun ω => Term ω + Cash ω) P ∧
    MeasurableSet[𝓕.rightCont 0] {ω : Ω | τ ω ≠ 0} := by
  obtain ⟨hTermMeas, hCashI⟩ :=
    avram_jump6_original_canonical_true_stopped_reward_measurable_Cash_integrable
      X x C D hD w hw_cont hw_neg q k τ hτeq hτmeas hτstop
      W Cash Term hW hCash hTerm
  by_cases hTop : C = ⊤
  · obtain ⟨hSigma, hTermI, hTotal, hInitial⟩ :=
      avram_jump6_finiteactivity_topcap_HJB_actual_stopped_full_reward_L1
        X hX hBV hFinite q hq w C hC hw_cont hw0 hw_neg
        hw_smooth hw_hjb x hx hxc D hD hxpos k hk τ hτeq hτmeas
        hτstop W Cash Term hW hCash hTerm hCashI hTop hTermMeas
    exact ⟨hTermMeas, hCashI, hTermI, hTotal, hInitial⟩
  · obtain ⟨hSigma, hClockBound, hTermI, hTermMeas',
        hTotal, hJump⟩ :=
      avram_jump6_finitecap_activity_root_budget_source_preflight
        X hX hBV hFinite q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_hjb x hx hxc D hD hxpos k hk τ hτeq hτmeas hτstop
        W Cash Term hW hCash hTerm hCashI hTop
    have hInitial : MeasurableSet[𝓕.rightCont 0]
        {ω : Ω | τ ω ≠ 0} :=
      avram_ubv_finite12_positive_clock_initial_measurable τ hτstop
    exact ⟨hTermMeas, hCashI, hTermI, hTotal, hInitial⟩
