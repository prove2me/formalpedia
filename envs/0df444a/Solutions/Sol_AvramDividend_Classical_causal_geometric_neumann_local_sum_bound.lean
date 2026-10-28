-- Prove2me | solution 1 for AvramDividend.Classical.causal_geometric_neumann_local_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T21:42:02.538108+00:00
-- url     : https://prove2.me/submissions/8b8fdd11-d3be-4fea-ab57-8df11273e59e

import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real Set

/-- Local geometric term estimates bound every causal Neumann partial sum uniformly. -/
theorem solution
    (Q : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hQ : ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ s ∈ Ioc (0 : ℝ) x,
        ‖Q n s‖ ≤ C * ρ ^ n) :
    ∀ x : ℝ, ∃ D : ℝ, 0 ≤ D ∧
      ∀ m : ℕ, ∀ s ∈ Ioc (0 : ℝ) x,
        ‖(∑ i ∈ Finset.range (m + 1), Q i) s‖ ≤ D := by
  have hgeom (m : ℕ) :
      (∑ i ∈ Finset.range (m + 1), ρ ^ i) ≤ (1 - ρ)⁻¹ := by
    calc
      (∑ i ∈ Finset.range (m + 1), ρ ^ i) ≤ ∑' i : ℕ, ρ ^ i :=
        (summable_geometric_of_lt_one hρ0 hρ1).sum_le_tsum
          _ (fun i _ => pow_nonneg hρ0 i)
      _ = (1 - ρ)⁻¹ := tsum_geometric_of_lt_one hρ0 hρ1
  intro x
  obtain ⟨C, hC, hbound⟩ := hQ x
  refine ⟨C / (1 - ρ), div_nonneg hC (sub_nonneg.mpr (le_of_lt hρ1)), ?_⟩
  intro m s hs
  calc
    ‖(∑ i ∈ Finset.range (m + 1), Q i) s‖ =
        ‖∑ i ∈ Finset.range (m + 1), Q i s‖ := by simp only [Finset.sum_apply]
    _ ≤ ∑ i ∈ Finset.range (m + 1), C * ρ ^ i := by
      apply norm_sum_le_of_le
      intro i hi
      exact hbound i s hs
    _ = C * (∑ i ∈ Finset.range (m + 1), ρ ^ i) := by rw [Finset.mul_sum]
    _ ≤ C * (1 - ρ)⁻¹ := mul_le_mul_of_nonneg_left (hgeom m) hC
    _ = C / (1 - ρ) := by rw [div_eq_mul_inv]
