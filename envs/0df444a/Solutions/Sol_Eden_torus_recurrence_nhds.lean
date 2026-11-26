-- Prove2me | solution 1 for Eden.torus_recurrence_nhds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:16:45.993806+00:00
-- url     : https://prove2.me/submissions/0e808f0b-64cd-41bc-ac63-8b566bbdeb01

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
theorem _root_.solution (c : ℝ) (p : torus) {U : Set torus}
    (hU : U ∈ 𝓝 p) {R : ℝ} (_hR : 0 < R) :
    ∃ t : ℝ, R < t ∧ torusEvolution c t p ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨t, htR, ht, hd⟩ := torus_recurrence_dist c p.property hε R
  exact ⟨t, htR, hball hd⟩
end Eden
