-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_finite_activity_expected_positive_clock_reward_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T08:29:44.512264+00:00
-- url     : https://prove2.me/submissions/cfd3df8e-5846-49fb-9cd8-ac0d71578d7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_finite_activity_expected_positive_clock_reward_budget_case_zeroNu_topcap
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_finite_activity_expected_positive_clock_reward_budget_case_zeroNu_finitecap
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_finite_activity_expected_positive_clock_reward_budget_case_nonzeroNu_topcap
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_finite_activity_expected_positive_clock_reward_budget_case_nonzeroNu_finitecap
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false



/-- Four exhaustive and non-circular physical source regimes. -/
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
    MeasurableSet {ω : Ω | τ ω ≠ 0} ∧
    Integrable (fun ω => Term ω + Cash ω) P ∧
    (∫ ω in {η : Ω | τ η ≠ 0}, Term ω + Cash ω ∂P) ≤
      w x * (P {η : Ω | τ η ≠ 0}).toReal := by
  by_cases hNu : X.ν = 0
  · by_cases hTop : C = ⊤
    · exact AvramDividend.Classical.avram_jump6_B_finite_activity_expected_positive_clock_reward_budget_case_zeroNu_topcap X hX hBV hFinite q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_hjb x hx hxc D hD hxpos k hk τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm hCashI hNu hTop
    · exact AvramDividend.Classical.avram_jump6_B_finite_activity_expected_positive_clock_reward_budget_case_zeroNu_finitecap X hX hBV hFinite q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_hjb x hx hxc D hD hxpos k hk τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm hCashI hNu hTop
  · by_cases hTop : C = ⊤
    · exact AvramDividend.Classical.avram_jump6_B_finite_activity_expected_positive_clock_reward_budget_case_nonzeroNu_topcap X hX hBV hFinite q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_hjb x hx hxc D hD hxpos k hk τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm hCashI hNu hTop
    · exact AvramDividend.Classical.avram_jump6_B_finite_activity_expected_positive_clock_reward_budget_case_nonzeroNu_finitecap X hX hBV hFinite q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_hjb x hx hxc D hD hxpos k hk τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm hCashI hNu hTop
