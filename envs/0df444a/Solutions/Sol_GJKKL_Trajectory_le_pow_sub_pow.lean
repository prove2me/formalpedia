-- Prove2me | solution 1 for GJKKL.Trajectory.le_pow_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:10.574228+00:00
-- url     : https://prove2.me/submissions/5fc4d5b1-4b57-4a29-ae71-99e6dca970d8

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Functions

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory
open Finset
namespace GJKKL.Trajectory
theorem _root_.solution {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (j : ℕ) :
    (j + 1) * y ^ j * (x - y) ≤ x ^ (j + 1) - y ^ (j + 1) := by
  rw [← geom_sum₂_mul]
  have hsum : ∑ _i ∈ range (j + 1), y ^ j ≤ ∑ i ∈ range (j + 1), x ^ i * y ^ (j + 1 - 1 - i) := by
    refine sum_le_sum fun i hi => ?_
    have hi' := mem_range.mp hi
    calc y ^ j = y ^ i * y ^ (j + 1 - 1 - i) := by rw [← pow_add]; congr 1; omega
      _ ≤ x ^ i * y ^ (j + 1 - 1 - i) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy hxy _) (pow_nonneg hy _)
  rw [sum_const, card_range, nsmul_eq_mul] at hsum
  push_cast at hsum
  exact mul_le_mul_of_nonneg_right hsum (by linarith)
end GJKKL.Trajectory
