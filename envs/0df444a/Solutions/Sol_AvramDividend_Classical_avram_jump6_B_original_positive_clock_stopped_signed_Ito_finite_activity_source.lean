-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_positive_clock_stopped_signed_Ito_finite_activity_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T18:22:06.30159+00:00
-- url     : https://prove2.me/submissions/e55d3157-6c07-41f7-b566-323f864847a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_finite_activity_expected_positive_clock_reward_budget
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_event_expected_budget_supports_centered_ae
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

/-- Full finite-activity root certificate reduced to the actual expected HJB budget. -/
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
    (hCashI : Integrable Cash P) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, τ ω = 0 → M ω = 0) ∧
      (∀ᵐ ω ∂P, τ ω = 0 → G ω = 0) ∧
      (∀ᵐ ω ∂P, τ ω = 0 → H ω = 0) ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, τ ω ≠ 0 →
        Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨hA, hFI, hBudget⟩ :=
    AvramDividend.Classical.avram_jump6_B_finite_activity_expected_positive_clock_reward_budget X hX hBV hFinite q hq w C hC hw_cont hw0 hw_neg hw_smooth
    hw_hjb x hx hxc D hD hxpos k hk τ hτeq hτmeas hτstop W Cash Term
    hW hCash hTerm hCashI
  obtain ⟨M, hMI, hMMean, hMZero, hMDom⟩ :=
    avram_jump6_B_event_expected_budget_supports_centered_ae
      {ω : Ω | τ ω ≠ 0} hA
      (fun ω => Term ω + Cash ω) hFI (w x) hBudget
  refine ⟨M, (fun _ : Ω => (0 : ℝ)), (fun _ : Ω => (0 : ℝ)),
    hMI, by simp, by simp, hMMean, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hMZero] with ω hω hz
    exact hω (by simp [hz])
  · filter_upwards with ω
    intro _
    rfl
  · filter_upwards with ω
    intro _
    rfl
  · filter_upwards with ω
    norm_num
  · filter_upwards [hMDom] with ω hω hpos
    have hBound := hω (show ω ∈ {η : Ω | τ η ≠ 0} from hpos)
    simpa using hBound
