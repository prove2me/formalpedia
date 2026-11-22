-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_finite_activity_expected_positive_clock_reward_budget_case_zeroNu_topcap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T08:42:23.54746+00:00
-- url     : https://prove2.me/submissions/5a9da87d-a11f-437a-b1f1-f01971b7c60d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_finiteactivity_anycap_canonical_true_stopped_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_zeroNu_topcap_true_positiveclock_HJB_expected_reward_of_full_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_topcap_w_nonnegative_everywhere
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_ubv_hjb_implies_right_dividend_secant
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine Gaussian-only topcap original reward budget branch. -/
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
    (hNuZero : X.ν = 0) (hTop : C = ⊤) :
    MeasurableSet {ω : Ω | τ ω ≠ 0} ∧
    Integrable (fun ω => Term ω + Cash ω) P ∧
    (∫ ω in {η : Ω | τ η ≠ 0}, Term ω + Cash ω ∂P) ≤
      w x * (P {η : Ω | τ η ≠ 0}).toReal := by
  classical
  obtain ⟨_hTermM, _hCashI, _hTermI, hRewardI, hEvent⟩ :=
    avram_jump6_finiteactivity_anycap_canonical_true_stopped_reward_L1
      X hX hBV hFinite q hq w C hC hw_cont hw0
      hw_neg hw_smooth hw_hjb x hx hxc D hD hxpos
      k hk τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
  have hGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hyC
    obtain ⟨hI, hEq⟩ := hw_hjb y hy hyC
    refine ⟨hI, ?_⟩
    exact (le_max_left _ _).trans (le_of_eq hEq)
  have hGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y := by
    intro y hy hyC
    have hEq := (hw_hjb y hy hyC).2
    have h := (le_max_right _ _).trans (le_of_eq hEq)
    linarith
  have hNonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by
    intro ω t _ _
    exact avram_ubv_top9_original_topcap_w_nonnegative_everywhere
      w C hTop hw0 hw_cont hw_neg hw_smooth hGrad
      (riskProcess X x D t ω)
  have hJump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) :=
    avram_jump6_original_ubv_hjb_implies_right_dividend_secant
      X hBV q w C hC hw_cont hw_smooth hw_hjb x hxc D hD
  obtain ⟨_hEvent0, hBound⟩ :=
    avram_jump6_original_zeroNu_topcap_true_positiveclock_HJB_expected_reward_of_full_L1
      X hX hBV hNuZero q hq w C hC hTop
      hw0 hw_cont hw_neg hw_smooth hGen hGrad
      x hxpos hxc D hD hNonneg hJump
      k hk τ hτeq hτmeas hτstop W Cash Term
      (by
        intro ω
        by_cases h : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
        · simpa only [if_pos h] using hW ω
        · simpa only [if_neg h] using hW ω)
      hCash hTerm hRewardI
  exact ⟨(𝓕.rightCont.le 0) _ hEvent, hRewardI, hBound⟩

