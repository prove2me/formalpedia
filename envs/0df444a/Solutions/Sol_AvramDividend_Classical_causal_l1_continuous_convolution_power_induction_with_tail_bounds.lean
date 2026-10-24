-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_continuous_convolution_power_induction_with_tail_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:09:41.723137+00:00
-- url     : https://prove2.me/submissions/4d30d138-2410-43de-8d6e-7a2cd75ed058

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_integrable_causal_convolution
import Theorems.Thm_AvramDividend_Classical_causal_convolution_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_continuousOn_positive_causal_convolution_of_locally_bounded_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Local continuity propagates inductively through positive-time L1
convolution powers when their pointwise quadratic bounds hold. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hκint : Integrable κ volume)
    (hκcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκbound : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume)
    (hFnonneg : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x)
    (hFpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    ∀ n : ℕ, ContinuousOn (F n) (Ioi (0 : ℝ)) := by
  have hmain : ∀ n : ℕ,
      Integrable (F n) volume ∧
      (∀ x : ℝ, x ≤ 0 → F n x = 0) ∧
      ContinuousOn (F n) (Ioi (0 : ℝ)) := by
    intro n
    induction n with
    | zero =>
        rw [hF0]
        exact ⟨hκint, hκzero, hκcont⟩
    | succ n ih =>
        obtain ⟨hFnint, hFnzero, hFncont⟩ := ih
        have hFnbound : ∀ ε : ℝ, 0 < ε →
            ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |F n x| ≤ M := by
          intro ε hε
          refine ⟨((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / ε, ?_⟩
          intro x hx
          have hpos : 0 ≤ F n x :=
            hFnonneg n x (le_trans (le_of_lt hε) hx)
          rw [abs_of_nonneg hpos]
          have hcoeff : 0 ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) :=
            mul_nonneg (sq_nonneg _) (pow_nonneg hρ _)
          exact (hFpoint n x (lt_of_lt_of_le hε hx)).trans
            (div_le_div_of_nonneg_left hcoeff hε hx)
        have hnextint : Integrable (F (n + 1)) volume := by
          rw [hFsucc n]
          exact integrable_causal_convolution κ (F n) hκint hFnint
        have hnextzero : ∀ x : ℝ, x ≤ 0 → F (n + 1) x = 0 := by
          intro x hx
          rw [hFsucc n]
          exact causal_convolution_zero_nonpositive κ (F n)
            hκzero hFnzero x hx
        have hnextcont : ContinuousOn (F (n + 1)) (Ioi (0 : ℝ)) := by
          rw [hFsucc n]
          exact continuousOn_positive_causal_convolution_of_locally_bounded_integrable
            κ (F n) hκint hFnint hκcont hFncont
            hκzero hFnzero hκbound hFnbound
        exact ⟨hnextint, hnextzero, hnextcont⟩
  exact fun n => (hmain n).2.2
