-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.isOpen_rightHalfPlane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:29.166281+00:00
-- url     : https://prove2.me/submissions/33847b9b-5689-417a-91a8-fd7563e1a7d2

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ExpChaotic_HalfPlane
import Definitions.Def_ExpChaotic_RealAxis

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re
end ExponentialJuliaSetMisiurewicz
