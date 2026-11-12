-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger158_finite_original_discounted_generator_grid_uniform_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:35:23.448653+00:00
-- url     : https://prove2.me/submissions/f73edc10-de94-4e70-9d6f-54af0e80a414

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section
theorem solution
    (m n : ℕ) (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hmδ : (m : ℝ) * δ ≤ (n : ℝ))
    (F : ℕ → ℝ) (hF : ∀ i ∈ Finset.range m, |F i| ≤ B) :
    |Finset.sum (Finset.range m) (fun i => δ * F i)| ≤ (n : ℝ) * B := by
  have hc : ∀ i ∈ Finset.range m, |δ * F i| ≤ δ * B := by
    intro i hi
    rw [abs_mul, abs_of_nonneg hδ]
    exact mul_le_mul_of_nonneg_left (hF i hi) hδ
  calc
    |Finset.sum (Finset.range m) (fun i => δ * F i)| ≤
        Finset.sum (Finset.range m) (fun i => |δ * F i|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ Finset.sum (Finset.range m) (fun _ => δ * B) :=
      Finset.sum_le_sum hc
    _ = (m : ℝ) * (δ * B) := by simp [mul_comm]
    _ = ((m : ℝ) * δ) * B := by ring
    _ ≤ (n : ℝ) * B := mul_le_mul_of_nonneg_right hmδ hB
