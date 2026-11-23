-- Prove2me | solution 1 for Experiments.geometric_average_near_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:01:15.277473+00:00
-- url     : https://prove2.me/submissions/f0aeba56-791e-4711-86ca-dc3e1fd0df7a

import Mathlib
import Definitions.Def_Experiments_GeneratorBound

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
namespace Experiments
theorem _root_.solution (x : A) {n : ℕ} (hn : 0 < n)
    (hx : ∀ k ∈ Finset.range n, ‖x ^ k - 1‖ ≤ (1 / 2 : ℝ)) :
    ‖(n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, x ^ k) - 1‖ ≤ (1 / 2 : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcount : (∑ _k ∈ Finset.range n, (1 : A)) = (n : ℝ) • (1 : A) := by
    simp [Algebra.smul_def]
  have havg :
      (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, (x ^ k - 1)) =
        (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, x ^ k) - 1 := by
    rw [Finset.sum_sub_distrib, hcount, smul_sub, smul_smul,
      inv_mul_cancel₀ hn', one_smul]
  rw [← havg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by exact_mod_cast hn))]
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, ‖x ^ k - 1‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (n : ℝ)⁻¹ * ∑ _k ∈ Finset.range n, (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hx) (by positivity)
    _ = _ := by simp [hn']
end Experiments
