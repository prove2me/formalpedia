-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.not_equicontinuousAt_sphericalExpIterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:17:50.248182+00:00
-- url     : https://prove2.me/submissions/e8fd8a3c-61ab-4061-84cd-6311c0a656a1

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
    ¬ EquicontinuousAt sphericalExpIterate z := by
  apply not_equicontinuousAt_expIterate_comp
    (q := fun w : ℂ => (w : OnePoint ℂ)) _ z
  exact fun h => (by norm_num : (1 : ℂ) ≠ 2) (OnePoint.coe_injective h)
end ExponentialJuliaSetMisiurewicz
