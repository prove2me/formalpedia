-- Prove2me | solution 1 for DeletedPrimes.tendsto_log_two_mul_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:08:12.821355+00:00
-- url     : https://prove2.me/submissions/7b6372fa-9486-4120-b14c-da3ef64863fd

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution :
    Tendsto (fun x : ℝ => Real.log (2 * x) / Real.log x) atTop (𝓝 1) := by
  have h : Tendsto (fun x : ℝ => Real.log 2 * (Real.log x)⁻¹ + 1) atTop (𝓝 (Real.log 2 * 0 + 1)) :=
    (Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul _).add_const 1
  rw [mul_zero, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [Real.log_mul (by norm_num) (by linarith)]
  field_simp
end DeletedPrimes
