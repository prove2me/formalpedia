-- Prove2me | solution 1 for GJKKL.Trajectory.pow_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:42:53.001431+00:00
-- url     : https://prove2.me/submissions/f8ae001a-5159-4762-8296-fe62ae1cc5cb

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
    x ^ (j + 1) - y ^ (j + 1) ≤ (j + 1) * x ^ j * (x - y) := by
  rw [← geom_sum₂_mul]
  have hx : 0 ≤ x := hy.trans hxy
  have hsum : ∑ i ∈ range (j + 1), x ^ i * y ^ (j + 1 - 1 - i) ≤ ∑ _i ∈ range (j + 1), x ^ j := by
    refine sum_le_sum fun i hi => ?_
    have hi' := mem_range.mp hi
    calc x ^ i * y ^ (j + 1 - 1 - i) ≤ x ^ i * x ^ (j + 1 - 1 - i) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hxy _) (pow_nonneg hx _)
      _ = x ^ j := by rw [← pow_add]; congr 1; omega
  rw [sum_const, card_range, nsmul_eq_mul] at hsum
  push_cast at hsum
  exact mul_le_mul_of_nonneg_right hsum (by linarith)
end GJKKL.Trajectory
