-- Prove2me | solution 1 for GaussianPerimeter.capNormalizer_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:09:18.530483+00:00
-- url     : https://prove2.me/submissions/60a7ac18-4561-480b-b56b-44300fbfcb2a

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Theorems.Thm_GaussianPerimeter_capProfile_continuous

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Interval Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) : 0 < capNormalizer n := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((capProfile_continuous hn).intervalIntegrable _ _) (fun x hx => ?_) (by norm_num)
  unfold capProfile
  apply Real.rpow_pos_of_pos
  have hx1 : -1 < x := hx.1
  have hx2 : x < 1 := hx.2
  nlinarith [mul_pos (by linarith : 0 < 1 + x) (by linarith : 0 < 1 - x)]
end GaussianPerimeter
