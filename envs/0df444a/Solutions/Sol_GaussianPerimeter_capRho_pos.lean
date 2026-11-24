-- Prove2me | solution 1 for GaussianPerimeter.capRho_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:08:36.479236+00:00
-- url     : https://prove2.me/submissions/aada3159-5654-4b24-97fb-9749b44395a2

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_GaussianPerimeter_CapAsymptotics

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Interval Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    0 < capRho a n := by
  unfold capRho
  exact mul_pos ha (Real.sqrt_pos.2 (Real.sqrt_pos.2 (by exact_mod_cast hn)))
end GaussianPerimeter
