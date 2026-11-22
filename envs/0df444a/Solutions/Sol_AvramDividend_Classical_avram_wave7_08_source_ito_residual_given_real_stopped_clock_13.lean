-- Prove2me | solution 13 for AvramDividend.Classical.avram_wave7_08_source_ito_residual_given_real_stopped_clock
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:28:46.295386+00:00
-- url     : https://prove2.me/submissions/79145c28-a26b-4b67-8a74-2828e4fa89dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_original_stopped_source_given_bounded_levy_exponential_clock_calculus
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_exp_mean_gt_one_of_q_lt_psi
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_exp_mean_ge_one_of_q_le_psi
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_exp_mean_lt_one_of_psi_lt_q
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_exp_mean_antitone_in_h_of_psi_le_q
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_exp_mean_antitone_in_discount
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_exp_mean_monotone_in_h_of_q_le_psi
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_increment_time_semigroup
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_exp_mean_one_of_psi_eq_q
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_exp_mean_le_one_of_psi_le_q
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

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
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∃ W Cash Term M G H : Ω → ℝ,
      (∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
        else riskProcess X x D (τ ω) ω) ∧
      (∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) ∧
      AEStronglyMeasurable Term P ∧
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by
  apply AvramDividend.Classical.avram_bridge20261122_original_stopped_source_given_bounded_levy_exponential_clock_calculus X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop
  exact ⟨AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_gt_one_of_q_lt_psi X,
    AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_ge_one_of_q_le_psi X,
    AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_lt_one_of_psi_lt_q X,
    AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_antitone_in_h_of_psi_le_q X,
    AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_antitone_in_discount X,
    AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_monotone_in_h_of_q_le_psi X,
    AvramDividend.Classical.levy_bounded_stopping_discounted_increment_time_semigroup X,
    AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_one_of_psi_eq_q X,
    AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_le_one_of_psi_le_q X⟩
