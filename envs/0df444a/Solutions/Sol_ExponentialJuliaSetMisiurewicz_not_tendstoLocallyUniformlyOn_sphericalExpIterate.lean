-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.not_tendstoLocallyUniformlyOn_sphericalExpIterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:17:00.867796+00:00
-- url     : https://prove2.me/submissions/e8a48a76-c2e4-4ee6-b5f9-02dc7e2c330e

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Spherical
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_tendstoLocallyUniformlyOn_expIterate_comp

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (g : ℂ → RiemannSphere) :
    ¬ TendstoLocallyUniformlyOn (fun n => sphericalExpIterate (φ n)) g atTop U := by
  apply not_tendstoLocallyUniformlyOn_expIterate_comp
    (q := fun w : ℂ => (w : OnePoint ℂ)) OnePoint.continuous_coe _ hU hUne hφ g
  exact fun h => (by norm_num : (1 : ℂ) ≠ 2) (OnePoint.coe_injective h)
end ExponentialJuliaSetMisiurewicz
