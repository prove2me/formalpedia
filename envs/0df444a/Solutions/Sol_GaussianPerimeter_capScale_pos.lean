-- Prove2me | solution 1 for GaussianPerimeter.capScale_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:26:52.096742+00:00
-- url     : https://prove2.me/submissions/cccb65f4-7793-4cc3-ba1c-e94955a1b7ca

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Theorems.Thm_GaussianPerimeter_capRho_pos

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Interval Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    0 < capScale a n := by
  unfold capScale
  have := capRho_pos ha hn
  positivity
end GaussianPerimeter
