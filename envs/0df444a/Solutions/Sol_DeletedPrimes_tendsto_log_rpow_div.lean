-- Prove2me | solution 1 for DeletedPrimes.tendsto_log_rpow_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:55:28.746751+00:00
-- url     : https://prove2.me/submissions/11aeadb1-2535-47fa-9e6d-3ee6b4767491

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (b : ℝ) :
    Tendsto (fun x : ℝ => Real.log (x ^ b) / Real.log x) atTop (𝓝 b) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  rw [Real.log_rpow (by linarith), mul_div_assoc, div_self (Real.log_pos hx).ne', mul_one]
end DeletedPrimes
