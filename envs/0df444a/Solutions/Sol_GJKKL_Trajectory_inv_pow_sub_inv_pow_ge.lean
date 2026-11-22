-- Prove2me | solution 1 for GJKKL.Trajectory.inv_pow_sub_inv_pow_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:11.90383+00:00
-- url     : https://prove2.me/submissions/0c69f228-34a0-4976-803c-dd196f61ff2e

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Theorems.Thm_GJKKL_Trajectory_le_pow_sub_pow

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory
open Finset
namespace GJKKL.Trajectory
theorem _root_.solution {x y : ℝ} (hy : 0 < y) (hxy : y ≤ x) (B : ℕ) :
    (B : ℝ) * (x - y) / x ^ (B + 1) ≤ 1 / y ^ B - 1 / x ^ B := by
  have hx : 0 < x := hy.trans_le hxy
  rcases B with _ | B
  · simp
  have hxB : 0 < x ^ (B + 1) := pow_pos hx _
  have hyB : 0 < y ^ (B + 1) := pow_pos hy _
  have key := le_pow_sub_pow hy.le hxy B
  rw [div_sub_div _ _ hyB.ne' hxB.ne', le_div_iff₀ (mul_pos hyB hxB)]
  have hyx : y ^ B ≤ x ^ B := pow_le_pow_left₀ hy.le hxy B
  -- `B' (x-y)/x^{B'+1} * (y^{B'} x^{B'}) = B' (x-y) y^{B'}/x ≤ B' (x-y) y^B ≤ x^{B'} - y^{B'}`
  have hxy0 : 0 ≤ x - y := by linarith
  have h1 : ((B + 1 : ℕ) : ℝ) * (x - y) / x ^ (B + 1 + 1) * (y ^ (B + 1) * x ^ (B + 1)) =
      ((B + 1 : ℕ) : ℝ) * (x - y) * y ^ B * (y / x) := by
    field_simp; ring
  rw [h1]
  have hyx1 : y / x ≤ 1 := (div_le_one hx).mpr hxy
  have h2 : ((B + 1 : ℕ) : ℝ) * (x - y) * y ^ B * (y / x) ≤
      ((B + 1 : ℕ) : ℝ) * (x - y) * y ^ B :=
    mul_le_of_le_one_right (by positivity) hyx1
  have h3 : 1 * x ^ (B + 1) - y ^ (B + 1) * 1 = x ^ (B + 1) - y ^ (B + 1) := by ring
  rw [h3]
  push_cast at h2 ⊢
  nlinarith
end GJKKL.Trajectory
