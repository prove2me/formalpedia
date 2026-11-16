-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_scaled_factorial_coeff_integrable_mean_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:42:37.421233+00:00
-- url     : https://prove2.me/submissions/543126b4-bec9-4252-a230-065cabca085c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a25_positive_factorial_moments_imply_integrable_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Real AvramDividend.Classical
open scoped NNReal ENNReal Nat
noncomputable section

/-- Scaled factorial coefficients have the expected integrable means. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (r : ℝ≥0) (hr : 0 < r)
    (hMom : ∀ n : ℕ,
      (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) = (r : ℝ) ^ n)
    (z : ℝ) :
    ∀ n : ℕ,
      Integrable (fun ω =>
        (Nat.descFactorial (K ω) n : ℝ) * (z ^ n / (n.factorial : ℝ))) P ∧
      (∫ ω, (Nat.descFactorial (K ω) n : ℝ) *
          (z ^ n / (n.factorial : ℝ)) ∂P) =
        ((r : ℝ) * z) ^ n / (n.factorial : ℝ) := by
  have hInt :=
    avram_a25_positive_factorial_moments_imply_integrable_20261115
      P K r hr hMom
  intro n
  constructor
  · exact (hInt n).mul_const _
  · rw [integral_mul_const, hMom n, mul_pow]
    ring
