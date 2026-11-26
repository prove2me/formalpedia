-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.norm_deriv_le_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:44.472157+00:00
-- url     : https://prove2.me/submissions/5b237f97-f84e-4ded-82d5-447f9e8e7cc8

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Definitions.Def_ExpChaotic_StripGeometry
import Definitions.Def_ExpChaotic_HalfPlane

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {f : ℂ → ℂ} {U : Set ℂ} {M r : ℝ} {z : ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hr : 0 < r) (hzr : closedBall z r ⊆ U)
    (hb : ∀ w ∈ U, ‖f w‖ ≤ M) :
    ‖deriv f z‖ ≤ M / r := by
  rw [← Complex.cderiv_eq_deriv hU hf hr hzr]
  exact Complex.norm_cderiv_le hr
    (fun w hw => hb w (hzr (sphere_subset_closedBall hw)))
end ExponentialJuliaSetMisiurewicz
