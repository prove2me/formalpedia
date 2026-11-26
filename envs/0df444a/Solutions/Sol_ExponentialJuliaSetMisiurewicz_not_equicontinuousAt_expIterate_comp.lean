-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.not_equicontinuousAt_expIterate_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:16:58.189045+00:00
-- url     : https://prove2.me/submissions/66e574e0-6310-49ca-840d-4c6d26ce9173

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
theorem _root_.solution
    {Y : Type*} [UniformSpace Y] [T0Space Y]
    {q : ℂ → Y} (hq : q 1 ≠ q 2) (z : ℂ) :
    ¬ EquicontinuousAt (fun n w => q (expIterate n w)) z := by
  intro h
  apply hq
  -- Equicontinuity would force the two distinct target values into every entourage.
  apply eq_of_uniformity
  intro W hW
  obtain ⟨V, hV, hpair⟩ := equicontinuousAt_iff_pair.mp h W hW
  obtain ⟨U, hUV, hU, hxU⟩ := _root_.mem_nhds_iff.mp hV
  -- At a common sufficiently late time, points of this small neighborhood hit both targets.
  obtain ⟨N, hN⟩ := eventually_hits_one_and_two hU ⟨z, hxU⟩
  obtain ⟨⟨a, ha, h₁⟩, ⟨b, hb, h₂⟩⟩ := hN N le_rfl
  have hab := hpair a (hUV ha) b (hUV hb) N
  simpa only [h₁, h₂] using hab
end ExponentialJuliaSetMisiurewicz
