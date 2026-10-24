-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_convolution_power_sequence_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:34:11.798049+00:00
-- url     : https://prove2.me/submissions/45974241-2e2a-4ee5-8f9b-eb7634c519ee

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_integrable
import Theorems.Thm_AvramDividend_Classical_causal_l1_positive_convolution_mass_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Every positive-time L1 kernel generates integrable causal powers with multiplicative mass. -/
theorem solution
    (κ : ℝ → ℝ)
    (hκ : IntegrableOn κ (Ioi (0 : ℝ)) volume) :
    ∃ F : ℕ → ℝ → ℝ,
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
          κ s * F n (x - s) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ,
        (∫ x in Ioi (0 : ℝ), F (n + 1) x ∂volume) =
        (∫ x in Ioi (0 : ℝ), κ x ∂volume) *
          (∫ x in Ioi (0 : ℝ), F n x ∂volume)) := by
  let F : ℕ → ℝ → ℝ :=
    fun n => Nat.rec κ
      (fun _ f x => ∫ s in Ioc (0 : ℝ) x,
        κ s * f (x - s) ∂volume) n
  have hzero : F 0 = κ := rfl
  have hsucc : ∀ n : ℕ, F (n + 1) =
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        κ s * F n (x - s) ∂volume) := by
    intro n
    rfl
  have hInt : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume := by
    intro n
    induction n with
    | zero => simpa only [hzero] using hκ
    | succ n ih =>
        rw [hsucc n]
        have hκ0 : IntegrableOn (fun t : ℝ => Real.exp (-(0 * t)) * κ t)
            (Ioi (0 : ℝ)) volume := by simpa using hκ
        have hF0 : IntegrableOn (fun t : ℝ => Real.exp (-(0 * t)) * F n t)
            (Ioi (0 : ℝ)) volume := by simpa using ih
        simpa using
          (AvramDividend.Classical.positive_causal_convolution_laplace_integrable
            κ (F n) 0 hκ0 hF0)
  refine ⟨F, hzero, hsucc, hInt, ?_⟩
  intro n
  rw [hsucc n]
  exact AvramDividend.Classical.causal_l1_positive_convolution_mass_product
    κ (F n) hκ (hInt n)
