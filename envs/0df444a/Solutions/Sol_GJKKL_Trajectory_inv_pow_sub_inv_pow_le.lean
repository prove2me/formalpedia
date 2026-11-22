-- Prove2me | solution 1 for GJKKL.Trajectory.inv_pow_sub_inv_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:23.81012+00:00
-- url     : https://prove2.me/submissions/1684ea6a-7989-4d05-a4e9-17c50df9a385

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Theorems.Thm_GJKKL_Trajectory_pow_sub_pow_le

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory
open Finset
namespace GJKKL.Trajectory
theorem _root_.solution {x y : ℝ} (hy : 0 < y) (hxy : y ≤ x) (B : ℕ) :
    1 / y ^ B - 1 / x ^ B ≤ (B : ℝ) * (x - y) / (x * y ^ B) := by
  have hx : 0 < x := hy.trans_le hxy
  rcases B with _ | B
  · simp
  have hxB : 0 < x ^ (B + 1) := pow_pos hx _
  have hyB : 0 < y ^ (B + 1) := pow_pos hy _
  have key := pow_sub_pow_le hy.le hxy B
  rw [div_sub_div _ _ hyB.ne' hxB.ne', div_le_div_iff₀ (mul_pos hyB hxB) (mul_pos hx hyB)]
  have h3 : (1 * x ^ (B + 1) - y ^ (B + 1) * 1) * (x * y ^ (B + 1)) =
      (x ^ (B + 1) - y ^ (B + 1)) * (x * y ^ (B + 1)) := by ring
  rw [h3]
  have h4 : ((B + 1 : ℕ) : ℝ) * (x - y) * (y ^ (B + 1) * x ^ (B + 1)) =
      ((B + 1 : ℕ) : ℝ) * x ^ B * (x - y) * (x * y ^ (B + 1)) := by ring
  rw [h4]
  push_cast at key ⊢
  exact mul_le_mul_of_nonneg_right key (by positivity)
end GJKKL.Trajectory
