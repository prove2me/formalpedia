-- Prove2me | solution 2 for GaussianPerimeter.capRho_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:58.015132+00:00
-- url     : https://prove2.me/submissions/eb3b139b-6dbe-4a26-acbe-786c280bf10c

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
theorem _root_.solution (a : ℝ) (n : ℕ) :
    capRho a n ^ 2 = a ^ 2 * Real.sqrt (n : ℝ) := by
  rw [capRho, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
end GaussianPerimeter
