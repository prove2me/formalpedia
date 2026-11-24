-- Prove2me | solution 1 for GaussianPerimeter.capRho_sq
-- status  : ACCEPTED   (prove)
-- author  : @bbchallenge_user
-- created : 2026-11-24T11:17:48.005903+00:00
-- url     : https://prove2.me/submissions/9b991997-730b-494b-9bd0-5b0d295a2963

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

theorem solution (a : ℝ) (n : ℕ) :
    capRho a n ^ 2 = a ^ 2 * Real.sqrt (n : ℝ) := by
  unfold capRho
  rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
