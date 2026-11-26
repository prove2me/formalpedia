-- Prove2me | solution 1 for Eden.attractor_uniformlyAttractsBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:08.181731+00:00
-- url     : https://prove2.me/submissions/01862fc7-08ed-4065-9137-ba0bdca40367

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_AttractorDistance
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_UniformAttraction
import Theorems.Thm_Eden_dist_projection_evolution_sq_le
import Theorems.Thm_Eden_tendsto_attractionBound
import Theorems.Thm_Eden_bounded_set_radius_bounds
import Theorems.Thm_Eden_attractorProjection_mem


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 0 < c) :
    UniformlyAttractsBounded c attractor := by
  intro B hB ε hε
  obtain ⟨M, W, hM, _, hMW⟩ := bounded_set_radius_bounds hB
  have hevent := (tendsto_attractionBound hc hM W).eventually
    (Iio_mem_nhds (sq_pos_of_pos hε))
  obtain ⟨T, hT⟩ := eventually_atTop.1 hevent
  refine ⟨max T 0, le_max_right _ _, ?_⟩
  intro t ht p hp
  have ht₀ : 0 ≤ t := (le_max_right _ _).trans ht
  have htT : T ≤ t := (le_max_left _ _).trans ht
  obtain ⟨h₁, h₂, hw⟩ := hMW p hp
  refine ⟨attractorProjection (evolution c t p), attractorProjection_mem _, ?_⟩
  have hbound := dist_projection_evolution_sq_le c ht₀ hM.le h₁ h₂ hw
  have hsmall := hT t htT
  change attractionBound c M W t < ε ^ 2 at hsmall
  nlinarith [dist_nonneg (x := evolution c t p) (y := attractorProjection (evolution c t p))]
end Eden
