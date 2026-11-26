-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.not_isNormalSequenceOn_sphericalExpIterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:17:39.710247+00:00
-- url     : https://prove2.me/submissions/50fd3cbc-46f1-4672-ba5e-f5056c6faf99

import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Definitions.Def_ExpChaotic_Spherical
import Definitions.Def_ExpChaotic_Normality
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_tendstoLocallyUniformly_expIterate_comp


set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ¬ IsNormalSequenceOn sphericalExpIterate U := by
  intro hnormal
  obtain ⟨ψ, hψ, g, hg⟩ := hnormal id strictMono_id
  exact not_tendstoLocallyUniformly_expIterate_comp
    (q := fun w : ℂ => (w : RiemannSphere)) OnePoint.continuous_coe
    (fun h => (by norm_num : (1 : ℂ) ≠ 2) (OnePoint.coe_injective h)) hU hUne hψ g hg
end ExponentialJuliaSetMisiurewicz
