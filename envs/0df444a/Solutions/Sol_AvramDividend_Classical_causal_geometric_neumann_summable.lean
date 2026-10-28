-- Prove2me | solution 1 for AvramDividend.Classical.causal_geometric_neumann_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T21:47:27.007247+00:00
-- url     : https://prove2.me/submissions/aa1f5a82-910b-4286-ac89-840bcb5ba12b

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A pointwise geometric bound makes the Gaussian Neumann expansion summable. -/
theorem solution
    (Q : ℕ → ℝ → ℝ) (ρ x : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hQ : ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ‖Q n x‖ ≤ C * ρ ^ n) :
    Summable (fun n : ℕ => Q n x) := by
  obtain ⟨C, hC, hbound⟩ := hQ
  exact ((summable_geometric_of_lt_one hρ0 hρ1).mul_left C).of_norm_bounded hbound
