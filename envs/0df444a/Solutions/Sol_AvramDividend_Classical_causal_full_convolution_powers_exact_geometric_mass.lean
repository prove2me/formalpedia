-- Prove2me | solution 1 for AvramDividend.Classical.causal_full_convolution_powers_exact_geometric_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:24:57.714291+00:00
-- url     : https://prove2.me/submissions/653f2c79-d841-475c-99a5-435a21a4823c

import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_causal_real_convolution_equals_positive_interval_under_support
import Theorems.Thm_AvramDividend_Classical_causal_l1_positive_convolution_mass_product
import Mathlib.Tactic.SimpRw

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Each recursive causal convolution power has the exact geometric mass. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hFzero : F 0 = κ)
    (hFrec : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume)
    (hFi : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) :
    ∀ n : ℕ,
      (∫ x in Ioi (0 : ℝ), F n x ∂volume) =
        (∫ x in Ioi (0 : ℝ), κ x ∂volume) ^ (n + 1) := by
  have hFnzero :=
    causal_full_convolution_powers_zero_nonpositive κ F hκzero hFzero hFrec
  intro n
  induction n with
  | zero =>
      simp [hFzero]
  | succ n ih =>
      calc
        (∫ x in Ioi (0 : ℝ), F (n + 1) x ∂volume) =
            ∫ x in Ioi (0 : ℝ),
              (∫ y in Ioc (0 : ℝ) x, κ y * F n (x - y) ∂volume) ∂volume := by
                simp_rw [hFrec n,
                  causal_real_convolution_equals_positive_interval_under_support
                    κ (F n) hκzero (hFnzero n)]
        _ = (∫ x in Ioi (0 : ℝ), κ x ∂volume) *
            (∫ x in Ioi (0 : ℝ), F n x ∂volume) :=
              causal_l1_positive_convolution_mass_product κ (F n) hκL1 (hFi n)
        _ = (∫ x in Ioi (0 : ℝ), κ x ∂volume) ^ ((n + 1) + 1) := by
              rw [ih]
              simp [pow_succ, mul_comm, mul_assoc]
