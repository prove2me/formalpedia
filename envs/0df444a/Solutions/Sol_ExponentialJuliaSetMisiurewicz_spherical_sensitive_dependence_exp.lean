-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.spherical_sensitive_dependence_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:17:48.482797+00:00
-- url     : https://prove2.me/submissions/024407cb-c65c-4695-93b0-403afe6f5eb4

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Spherical
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_eventually_hits_one_and_two
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution :
    HasSensitiveDependenceVia
      (fun w : ℂ => riemannSphereUniformEquivUnitSphere (w : OnePoint ℂ)) := by
  let q : ℂ → sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun w => riemannSphereUniformEquivUnitSphere (w : OnePoint ℂ)
  have hq : q 1 ≠ q 2 := by
    intro h
    exact (by norm_num : (1 : ℂ) ≠ 2)
      (OnePoint.coe_injective (riemannSphereUniformEquivUnitSphere.injective h))
  refine ⟨dist (q 1) (q 2), dist_pos.mpr hq, fun U hU hUne => ?_⟩
  obtain ⟨N, hN⟩ := eventually_hits_one_and_two hU hUne
  obtain ⟨⟨z, hzU, hz⟩, ⟨w, hwU, hw⟩⟩ := hN N le_rfl
  refine ⟨N, z, hzU, w, hwU, ?_⟩
  simpa only [hz, hw, q] using le_rfl
end ExponentialJuliaSetMisiurewicz
