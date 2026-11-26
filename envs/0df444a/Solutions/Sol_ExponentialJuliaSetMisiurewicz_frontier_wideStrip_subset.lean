-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.frontier_wideStrip_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:21.137101+00:00
-- url     : https://prove2.me/submissions/1a25e4d9-80eb-4e7a-8115-064100fe847d

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
    frontier wideStrip ⊆ {z : ℂ | |z.im| = 2 * Real.pi} :=
  frontier_le_subset_eq (continuous_abs.comp Complex.continuous_im) continuous_const
end ExponentialJuliaSetMisiurewicz
