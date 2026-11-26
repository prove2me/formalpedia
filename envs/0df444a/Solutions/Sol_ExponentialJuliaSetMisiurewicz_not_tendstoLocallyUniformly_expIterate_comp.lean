-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.not_tendstoLocallyUniformly_expIterate_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:17:00.149845+00:00
-- url     : https://prove2.me/submissions/70647ebc-a69e-4b8a-9842-cae72eb3a7dc

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Spherical
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_tendstoLocallyUniformlyOn_expIterate_comp
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
theorem _root_.solution
    {Y : Type*} [UniformSpace Y] [T0Space Y]
    {q : ℂ → Y} (hqcont : Continuous q) (hq : q 1 ≠ q 2)
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (g : U → Y) :
    ¬ TendstoLocallyUniformly (fun n (z : U) => q (expIterate (φ n) z)) g atTop := by
  classical
  let g' : ℂ → Y := fun z => if h : z ∈ U then g ⟨z, h⟩ else q 1
  have hrestrict : (fun z : U => g' z) = g := by
    funext z
    simp [g', z.property]
  intro h
  apply not_tendstoLocallyUniformlyOn_expIterate_comp hqcont hq hU hUne hφ g'
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  change TendstoLocallyUniformly _ (fun z : U => g' z) atTop
  rwa [hrestrict]
end ExponentialJuliaSetMisiurewicz
