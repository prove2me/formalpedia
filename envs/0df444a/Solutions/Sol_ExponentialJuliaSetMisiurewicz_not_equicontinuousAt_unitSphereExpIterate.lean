-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.not_equicontinuousAt_unitSphereExpIterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:18:02.543008+00:00
-- url     : https://prove2.me/submissions/07cb637d-e838-46d6-880c-3217f830d00e

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Spherical
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_equicontinuousAt_expIterate_comp

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution (z : ℂ) :
    ¬ EquicontinuousAt
      (fun n w => riemannSphereUniformEquivUnitSphere (sphericalExpIterate n w)) z := by
  apply not_equicontinuousAt_expIterate_comp
    (q := fun w : ℂ => riemannSphereUniformEquivUnitSphere (w : OnePoint ℂ)) _ z
  intro h
  exact (by norm_num : (1 : ℂ) ≠ 2)
    (OnePoint.coe_injective (riemannSphereUniformEquivUnitSphere.injective h))
end ExponentialJuliaSetMisiurewicz
