-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.disjoint_frontier_centralStrip_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:43.822963+00:00
-- url     : https://prove2.me/submissions/385fcabd-bd5c-46d8-9729-a20b4d1feb8a

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
    Disjoint (frontier centralStrip) (piDoubleStrip ∩ rightHalfPlane) := by
  rw [Set.disjoint_left]
  rintro z hz ⟨hw, hh⟩
  have hfr : |z.im| = Real.pi / 3 := frontier_centralStrip_subset hz
  have hbig := abs_im_exp_gt_two_pi_of_frontier hfr hh
  have : |(Complex.exp z).im| ≤ Real.pi := hw.2
  nlinarith [Real.pi_pos]
end ExponentialJuliaSetMisiurewicz
