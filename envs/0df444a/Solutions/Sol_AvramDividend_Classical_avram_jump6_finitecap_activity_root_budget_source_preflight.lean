-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_finitecap_activity_root_budget_source_preflight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T18:57:15.127963+00:00
-- url     : https://prove2.me/submissions/5c14ca0a-a186-47cf-b7de-777fabeed7c2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finiteactivity_UBV_gaussian_sigma_positive
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
import Theorems.Thm_AvramDividend_Classical_avram_jump6_finitecap_original_stopped_reward_integrable
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_ubv_hjb_implies_right_dividend_secant
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source-specific finite-cap HJB preflight at the true stopped clock.
 All integrability and dividend-jump claims are discharged directly. -/
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
    (hCashI : Integrable Cash P)
    (hFiniteCap : C ≠ ⊤) :
    (0 < X.σ) ∧
    (∀ ω, τ ω ≤ (k : ℝ≥0)) ∧
    Integrable Term P ∧
    AEStronglyMeasurable Term P ∧
    Integrable (fun ω => Term ω + Cash ω) P ∧
    (∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hFiniteMass : X.ν (Iio (0 : ℝ)) < ⊤ :=
    lt_top_iff_ne_top.mpr hFinite
  have hSigma : 0 < X.σ :=
    avram_f6_original_finiteactivity_UBV_gaussian_sigma_positive
      X hBV hFiniteMass
  have hBound : ∀ ω, τ ω ≤ (k : ℝ≥0) :=
    (avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
      X x C D hD k hk τ τ hτeq (fun ω => le_refl (τ ω))).1
  have hTotal : Integrable (fun ω => Term ω + Cash ω) P :=
    avram_jump6_finitecap_original_stopped_reward_integrable
      X x C hFiniteCap hxc D hD q (le_of_lt hq)
      w hw_cont hw_neg k hk τ hτeq hτstop
      W Cash Term hW hCash hTerm
  have hTermI : Integrable Term P := by
    have hSub : Integrable
        (fun ω => (Term ω + Cash ω) - Cash ω) P :=
      hTotal.sub hCashI
    have hEq :
        (fun ω => (Term ω + Cash ω) - Cash ω) = Term := by
      funext ω
      ring
    simpa only [hEq] using hSub
  have hJump :
      ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) :=
    avram_jump6_original_ubv_hjb_implies_right_dividend_secant
      X hBV q w C hC hw_cont hw_smooth hw_hjb x hxc D hD
  exact ⟨hSigma, hBound, hTermI, hTermI.aestronglyMeasurable,
    hTotal, hJump⟩
