-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.frontier_expStrip_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:31.077011+00:00
-- url     : https://prove2.me/submissions/658f9216-78b7-49b3-b71d-d0233fb1a244

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
    frontier {z : ℂ | |(Complex.exp z).im| ≤ 2 * Real.pi}
      ⊆ {z : ℂ | |(Complex.exp z).im| = 2 * Real.pi} :=
  frontier_le_subset_eq
    (continuous_abs.comp (Complex.continuous_im.comp Complex.continuous_exp)) continuous_const
end ExponentialJuliaSetMisiurewicz
