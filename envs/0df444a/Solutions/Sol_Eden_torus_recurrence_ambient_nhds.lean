-- Prove2me | solution 1 for Eden.torus_recurrence_ambient_nhds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:34.700796+00:00
-- url     : https://prove2.me/submissions/16c4e047-62e7-46d9-845c-d86dbc4eb3f7

import Definitions.Def_Eden_TorusAngles
import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_Uniqueness
import Mathlib.Topology.MetricSpace.Cauchy
import Definitions.Def_Eden_TorusRecurrence
import Theorems.Thm_Eden_torus_recurrence_dist

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {p : PhaseSpace} (hp : p ∈ torus)
    {U : Set PhaseSpace} (hU : U ∈ 𝓝 p) {R : ℝ} (_hR : 0 < R) :
    ∃ t : ℝ, R < t ∧ evolution c t p ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨t, htR, ht, hd⟩ := torus_recurrence_dist c hp hε R
  exact ⟨t, htR, hball hd⟩
end Eden
