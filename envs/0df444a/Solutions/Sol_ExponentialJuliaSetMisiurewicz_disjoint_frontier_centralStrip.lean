-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.disjoint_frontier_centralStrip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:33.010112+00:00
-- url     : https://prove2.me/submissions/6bb6b3ac-843c-4328-9ebc-354ff9b4d556

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_frontier_centralStrip_subset
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_abs_im_exp_gt_two_pi_of_frontier

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution :
    Disjoint (frontier centralStrip) (doubleStrip ∩ rightHalfPlane) := by
  rw [Set.disjoint_left]
  rintro z hz ⟨hw, hh⟩
  have hfr : |z.im| = Real.pi / 3 := frontier_centralStrip_subset hz
  exact absurd hw.2 (not_le.mpr (abs_im_exp_gt_two_pi_of_frontier hfr hh))
end ExponentialJuliaSetMisiurewicz
