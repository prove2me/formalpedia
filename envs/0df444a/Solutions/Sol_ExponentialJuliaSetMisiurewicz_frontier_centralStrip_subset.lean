-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.frontier_centralStrip_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:25.834697+00:00
-- url     : https://prove2.me/submissions/d346c42a-ba43-40bf-8dab-f43a348ffd15

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
    frontier centralStrip ⊆ {z : ℂ | |z.im| = Real.pi / 3} := by
  have hcont : Continuous fun z : ℂ => |z.im| :=
    continuous_abs.comp Complex.continuous_im
  exact frontier_le_subset_eq hcont continuous_const
end ExponentialJuliaSetMisiurewicz
