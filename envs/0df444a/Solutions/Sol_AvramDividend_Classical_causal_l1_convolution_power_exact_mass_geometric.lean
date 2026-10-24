-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_convolution_power_exact_mass_geometric
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T13:59:31.706438+00:00
-- url     : https://prove2.me/submissions/6cc567bb-dfeb-4a22-8328-242f460f9a67

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_power_sequence_exists

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- The total positive-time mass of each causal convolution power is geometric. -/
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
        (∫ x in Ioi (0 : ℝ), F n x ∂volume) =
          (∫ x in Ioi (0 : ℝ), κ x ∂volume) ^ (n + 1)) := by
  obtain ⟨F, hzero, hsucc, hInt, hMass⟩ :=
    AvramDividend.Classical.causal_l1_convolution_power_sequence_exists κ hκ
  refine ⟨F, hzero, hsucc, hInt, ?_⟩
  intro n
  induction n with
  | zero =>
      simpa only [hzero, zero_add, pow_one]
  | succ n ih =>
      rw [hMass n, ih]
      simpa only [Nat.succ_eq_add_one, pow_succ] using
        (mul_comm (∫ x in Ioi (0 : ℝ), κ x ∂volume)
          ((∫ x in Ioi (0 : ℝ), κ x ∂volume) ^ (n + 1)))
