-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.frontier_expPiStrip_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:41.109498+00:00
-- url     : https://prove2.me/submissions/0e1cab2f-61af-4819-a98e-58c56c63bf85

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
    frontier {z : ℂ | |(Complex.exp z).im| ≤ Real.pi}
      ⊆ {z : ℂ | |(Complex.exp z).im| = Real.pi} :=
  frontier_le_subset_eq
    (continuous_abs.comp (Complex.continuous_im.comp Complex.continuous_exp)) continuous_const
end ExponentialJuliaSetMisiurewicz
