-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux3_ubv_finite_cap_original_stopped_ennreal_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:20:41.362212+00:00
-- url     : https://prove2.me/submissions/ec6aea57-60ea-4f3e-9b12-37207ff72f3b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f5_original_real_stopped_payoff_integrability_and_mean_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_all_cap_stopped_terminal_candidate_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-! Finite-cap case of original stopped real-to-ENNReal budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hFinite : C ≠ ⊤) :
    (0 ≤ w x) ∧ (∀ᵐ ω ∂P, 0 ≤ Term ω) ∧ (∀ᵐ ω ∂P, 0 ≤ Cash ω) ∧
    ((∫⁻ ω, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤ ENNReal.ofReal (w x)) := by
  have hBudget := avram_p4_f5_original_real_stopped_payoff_integrability_and_mean_budget
    X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop
    W Cash Term hW hCash hTerm hTermMeas hCashI
  rcases hBudget with ⟨hL1, hBudget⟩
  have hwx : 0 ≤ w x := by
    have hSecant := avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
      C w hw_cont hw_smooth hw_grad 0 x (le_refl _) hx.le hxc
    linarith
  have hTermPos : ∀ᵐ ω ∂P, 0 ≤ Term ω := by
    filter_upwards [] with ω
    rw [hTerm ω, hW ω]
    split_ifs
    · exact mul_nonneg (Real.exp_nonneg _)
        (avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative
          X w C hw0 hw_cont hw_neg hw_smooth hw_grad x hxc D hD ω (τ ω))
    · exact mul_nonneg (Real.exp_nonneg _)
        (avram_wave5_ubv_original_all_cap_stopped_terminal_candidate_nonnegative
          X w C hw0 hw_cont hw_neg hw_smooth hw_grad x hxc D hD ω (τ ω))
  have hCashPos : ∀ᵐ ω ∂P, 0 ≤ Cash ω := by
    filter_upwards [] with ω
    rw [hCash ω]
    exact ENNReal.toReal_nonneg
  have hSumPos : ∀ᵐ ω ∂P, 0 ≤ Term ω + Cash ω := by
    filter_upwards [hTermPos, hCashPos] with ω ht hc
    linarith
  refine ⟨hwx, hTermPos, hCashPos, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hL1 hSumPos]
  exact ENNReal.ofReal_le_ofReal hBudget
