-- Prove2me | solution 1 for GaussianPerimeter.fourthRoot_eq_rpow
-- status  : ACCEPTED   (prove)
-- author  : @bbchallenge_user
-- created : 2026-11-24T11:17:45.096807+00:00
-- url     : https://prove2.me/submissions/7c3a05ce-b715-4ab8-a79d-9961d1fe45fe

module
public import Definitions.Def_GaussianPerimeter_Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Definitions.Def_GaussianPerimeter_Scaling
set_option autoImplicit true
@[expose] public section
public section
open Filter
open scoped Topology
open GaussianPerimeter

theorem solution (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num
