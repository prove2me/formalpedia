-- Prove2me | solution 2 for GaussianPerimeter.fourthRoot_eq_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:23:08.789561+00:00
-- url     : https://prove2.me/submissions/d6e0b00e-04ac-4032-b10c-48b649929c92

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
namespace GaussianPerimeter
theorem _root_.solution (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num
end GaussianPerimeter
