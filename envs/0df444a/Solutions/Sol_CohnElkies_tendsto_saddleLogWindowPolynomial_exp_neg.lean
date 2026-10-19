-- Prove2me | solution 1 for CohnElkies.tendsto_saddleLogWindowPolynomial_exp_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/cbb59620-029f-49c7-bdbe-4720122e8a6a

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
theorem _root_.solution
    (C : ℝ) :
    Tendsto
      (fun t : ℝ =>
        (2 * (t / 8 + C) + (t / 8 + C) ^ 2) *
          Real.exp (-(3 / 4 : ℝ) * t))
      atTop (𝓝 0) := by
  have hscale :
      Tendsto
        (fun t : ℝ => (3 / 4 : ℝ) * t)
        atTop atTop :=
    tendsto_id.const_mul_atTop
      (by norm_num : (0 : ℝ) < 3 / 4)
  have h2base :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
      hscale
  have h2 :
      Tendsto
        (fun t : ℝ =>
          t ^ 2 * Real.exp (-(3 / 4 : ℝ) * t))
        atTop (𝓝 0) := by
    convert! h2base.const_mul ((4 / 3 : ℝ) ^ 2)
      using 1
    · funext t
      try dsimp
      have ha :
          -((3 / 4 : ℝ) * t) =
            (-(3 / 4 : ℝ)) * t := by ring
      rw [ha]
      ring
    · norm_num
  have h1base :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      hscale
  have h1 :
      Tendsto
        (fun t : ℝ =>
          t * Real.exp (-(3 / 4 : ℝ) * t))
        atTop (𝓝 0) := by
    convert! h1base.const_mul (4 / 3 : ℝ)
      using 1
    · funext t
      try dsimp
      have ha :
          -((3 / 4 : ℝ) * t) =
            (-(3 / 4 : ℝ)) * t := by ring
      rw [ha]
      ring
    · norm_num
  have h0 :
      Tendsto
        (fun t : ℝ =>
          Real.exp (-(3 / 4 : ℝ) * t))
        atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using!
      (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg
          (by norm_num : (-(3 / 4 : ℝ)) < 0)))
  have hpoly :=
    ((h2.const_mul (1 / 64 : ℝ)).add
      (h1.const_mul (C / 4 + 1 / 4))).add
        (h0.const_mul (C ^ 2 + 2 * C))
  convert! hpoly using 1
  · funext t
    ring
  · norm_num
end CohnElkies
