-- Prove2me | solution 1 for BirkhoffGlobalSection.locallyConvexSet_locallyPathConnected
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:39:59.028972+00:00
-- url     : https://prove2.me/submissions/a0e0be03-3d39-4b0a-b0e2-68fcba8818eb

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.ProperSpace

open scoped Topology
open Set Metric Filter
open BirkhoffGlobalSection


open BirkhoffGlobalSection NormedSpace Set Metric Filter
open scoped Topology unitInterval BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem solution (K : Set Phase)
    (hloc : ∀ x ∈ K, ∃ U : Set Phase, U ∈ 𝓝 x ∧ Convex ℝ (K ∩ U)) :
    LocallyPathConnectedSpace K := by
  refine ⟨fun x ↦ ⟨fun s ↦ ⟨fun hs ↦ ?_, fun ⟨t, ht⟩ ↦ mem_of_superset ht.1.1 ht.2⟩⟩⟩
  obtain ⟨t, ht⟩ := (mem_nhds_subtype K x s).mp hs
  obtain ⟨U, hU, hc⟩ := hloc x x.property
  obtain ⟨V, hV, hsub⟩ :=
    (LocallyConvexSpace.convex_basis (𝕜 := ℝ) x.1).mem_iff.mp (inter_mem ht.1 hU)
  refine ⟨(↑) ⁻¹' V, ⟨?_, ?_⟩, (preimage_mono (hsub.trans inter_subset_left)).trans ht.2⟩
  · exact continuousAt_subtype_val.preimage_mem_nhds hV.1
  · refine Subtype.preimage_coe_self_inter _ _ ▸ IsPathConnected.preimage_coe ?_ inter_subset_left
    have heq : K ∩ V = (K ∩ U) ∩ V := by
      ext y
      constructor
      · rintro ⟨hy, hv⟩
        exact ⟨⟨hy, (hsub hv).2⟩, hv⟩
      · rintro ⟨⟨hy, _⟩, hv⟩
        exact ⟨hy, hv⟩
    rw [heq]
    exact (hc.inter hV.2).isPathConnected ⟨x, ⟨x.property, mem_of_mem_nhds hU⟩,
      mem_of_mem_nhds hV.1⟩
