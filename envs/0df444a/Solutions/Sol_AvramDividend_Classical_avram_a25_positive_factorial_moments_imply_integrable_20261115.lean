-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_positive_factorial_moments_imply_integrable_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:32:51.908105+00:00
-- url     : https://prove2.me/submissions/e1ee1e8c-d538-455e-aba3-9899920940cb

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Nat
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (r : ℝ≥0) (hr : 0 < r)
    (hMom : ∀ n : ℕ,
      (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) = (r : ℝ) ^ n) :
    ∀ n : ℕ,
      Integrable (fun ω => (Nat.descFactorial (K ω) n : ℝ)) P := by
  intro n
  apply Integrable.of_integral_ne_zero
  rw [hMom n]
  exact ne_of_gt (pow_pos (NNReal.coe_pos.mpr hr) n)
