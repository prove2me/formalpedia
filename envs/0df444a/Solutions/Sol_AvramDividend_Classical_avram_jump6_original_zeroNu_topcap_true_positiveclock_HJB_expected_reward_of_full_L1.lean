-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_original_zeroNu_topcap_true_positiveclock_HJB_expected_reward_of_full_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T08:28:44.825859+00:00
-- url     : https://prove2.me/submissions/14f340e5-93b6-40d5-a8ea-415d91e6c5e6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_ubv_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_gaussian_masked_expected_topcap
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_canonical_true_stopped_reward_measurable_Cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
/-- For a genuine zero-jump original Gaussian Levy process and infinite cap,
the physical positive-clock expected nonlinear reward HJB bound follows from
the proved stopped Gaussian Itô ledger once the sole remaining L1 input is met. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hNuZero : X.ν = 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ) (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) (hRewardI : Integrable (fun ω => Term ω + Cash ω) P) :
    MeasurableSet[𝓕.rightCont 0] {ω : Ω | τ ω ≠ 0} ∧ (∫ ω in {η : Ω | τ η ≠ 0}, Term ω + Cash ω ∂P) ≤ w x * (P {η : Ω | τ η ≠ 0}).toReal := by
  letI : IsProbabilityMeasure P := X.isProbability
  let A : Set Ω := {ω | τ ω ≠ 0}
  have hA₀ : MeasurableSet[𝓕.rightCont 0] A :=
    avram_ubv_finite12_positive_clock_initial_measurable τ hτstop
  have hA : MeasurableSet A := (𝓕.rightCont.le 0) A hA₀
  obtain ⟨hTermM, hCashI⟩ :=
    avram_jump6_original_canonical_true_stopped_reward_measurable_Cash_integrable
      X x C D hD w hw_cont hw_neg q n τ hτeq hτmeas hτstop
      W Cash Term
      (by
        intro ω
        by_cases h : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
        · simpa only [if_pos h] using hW ω
        · simpa only [if_neg h] using hW ω)
      hCash hTerm
  have hσ : X.σ ≠ 0 :=
    ne_of_gt (avram_p4_f4_zero_levy_ubv_sigma_pos X hBV hNuZero)
  let F : ℕ → Ω → ℝ := fun _ ω => Term ω + Cash ω
  have hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by
    intro k ω
    change Term ω + Cash ω = _
    rw [hTerm ω, hCash ω, hW ω]
  have hWhole :
      (∫ ω, if τ ω = 0 then w x else Term ω + Cash ω ∂P) ≤
        w x := by
    simpa [F] using
      (avram_ubv_loc6_gaussian_masked_expected_topcap
        X hX hBV hσ hNuZero q hq w C hC hTop
        hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
        x hx hxc D hD hw_nonneg hjump
        n hn τ hτeq hτmeas hτstop W Cash Term
        (by
          intro ω
          by_cases h : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          · simpa only [if_pos h] using hW ω
          · simpa only [if_neg h] using hW ω)
        hCash hTerm hTermM hCashI
        (fun _ : ℕ => τ) F
        (fun _ => hτstop) (fun k ω => le_refl _)
        (by
          intro k ω
          by_cases h : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          · simpa only [if_pos h] using hFsource k ω
          · simpa only [if_neg h] using hFsource k ω)
        (fun _ => hRewardI) 0)
  have hMask : (fun ω => if τ ω = 0 then w x else Term ω + Cash ω) =
      (fun ω => (Aᶜ.indicator (fun _ => w x)) ω +
        (A.indicator (fun ω => Term ω + Cash ω)) ω) := by
    funext ω
    by_cases hω : τ ω = 0
    · simp [A, Set.indicator, hω]
    · simp [A, Set.indicator, hω]
  have hConstI : Integrable (Aᶜ.indicator (fun _ : Ω => w x)) P :=
    (integrable_const (w x)).indicator hA.compl
  have hRewardMasked : Integrable
      (A.indicator (fun ω => Term ω + Cash ω)) P :=
    hRewardI.indicator hA
  have hWholeSplit :
      (∫ ω in Aᶜ, (w x : ℝ) ∂P) +
      (∫ ω in A, Term ω + Cash ω ∂P) ≤ w x := by
    rw [hMask] at hWhole
    rw [integral_add hConstI hRewardMasked] at hWhole
    rw [integral_indicator hA.compl, integral_indicator hA] at hWhole
    exact hWhole
  have hConstSplit :
      (∫ ω in Aᶜ, (w x : ℝ) ∂P) +
      (∫ ω in A, (w x : ℝ) ∂P) = w x := by
    have h := integral_add_compl hA (show Integrable (fun _ : Ω => w x) P from integrable_const (w x))
    have hconst : (∫ _ω : Ω, (w x : ℝ) ∂P) = w x := by simp
    rw [hconst] at h
    linarith
  have hBound : (∫ ω in A, Term ω + Cash ω ∂P) ≤
      w x * (P A).toReal := by
    have hMain : (∫ ω in A, Term ω + Cash ω ∂P) ≤
        ∫ ω in A, (w x : ℝ) ∂P := by
      linarith
    simpa [setIntegral_const, smul_eq_mul, mul_comm, Measure.real] using hMain
  exact ⟨hA₀, hBound⟩
