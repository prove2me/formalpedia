-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.isClosed_centralStrip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:25.134246+00:00
-- url     : https://prove2.me/submissions/9580e494-defa-431c-abd9-96b2611bf278

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
theorem _root_.solution : IsClosed centralStrip :=
  isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
end ExponentialJuliaSetMisiurewicz
