-- Prove2me | solution 1 for CohnElkies.tendsto_upper_log_cubic_gaussian_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/023b5d6a-c05b-4463-8755-69a042e59a9a

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    Tendsto (fun x : ℝ =>
      (10 * Real.log x + x ^ 3) *
        Real.exp (-(x ^ 2) / 8))
      atTop (𝓝 (0 : ℝ)) := by
  have hupper :
      Tendsto (fun x : ℝ =>
        11 * ((x ^ 3 + 1) *
          Real.exp (-(x ^ 2) / 8)))
        atTop (𝓝 (0 : ℝ)) := by
    simpa using! tendsto_cubic_gaussian_atTop.const_mul (11 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    have hcube : 0 ≤ x ^ 3 := by positivity
    exact mul_nonneg (by nlinarith) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := by linarith
    have hlog := Real.log_le_sub_one_of_pos hxpos
    have hsquare : 0 ≤ x ^ 2 - 1 := by
      nlinarith [sq_nonneg (x - 1)]
    have hcube : x ≤ x ^ 3 := by
      nlinarith [mul_nonneg hxpos.le hsquare]
    have hfactor :
        10 * Real.log x + x ^ 3 ≤
          11 * (x ^ 3 + 1) := by
      nlinarith
    calc
      (10 * Real.log x + x ^ 3) *
          Real.exp (-(x ^ 2) / 8) ≤
        (11 * (x ^ 3 + 1)) *
          Real.exp (-(x ^ 2) / 8) :=
        mul_le_mul_of_nonneg_right hfactor
          (Real.exp_pos _).le
      _ = 11 * ((x ^ 3 + 1) *
          Real.exp (-(x ^ 2) / 8)) := by ring
end CohnElkies
