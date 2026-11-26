-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.frontier_piStrip_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:40.584902+00:00
-- url     : https://prove2.me/submissions/15fb12e5-3752-40e2-93e0-74c3f27281e4

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution :
    frontier piStrip ⊆ {z : ℂ | |z.im| = Real.pi} :=
  frontier_le_subset_eq (continuous_abs.comp Complex.continuous_im) continuous_const
end ExponentialJuliaSetMisiurewicz
