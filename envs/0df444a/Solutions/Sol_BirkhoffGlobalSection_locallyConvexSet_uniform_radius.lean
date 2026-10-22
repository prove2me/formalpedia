-- Prove2me | solution 1 for BirkhoffGlobalSection.locallyConvexSet_uniform_radius
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:39:59.887281+00:00
-- url     : https://prove2.me/submissions/04c8c8c1-1b65-4621-b0ca-f108c2f0edce

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

theorem solution (K A : Set Phase) (hA : IsCompact A)
    (hAK : A ⊆ K)
    (hloc : ∀ x ∈ K, ∃ U : Set Phase, U ∈ 𝓝 x ∧ Convex ℝ (K ∩ U)) :
    ∃ δ > 0, ∀ x ∈ A, Convex ℝ (K ∩ ball x δ) := by
  have hballs : ∀ x : K, ∃ r > 0, Convex ℝ (K ∩ ball (x : Phase) r) := by
    intro x
    obtain ⟨U, hU, hc⟩ := hloc x x.property
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
    refine ⟨r, hr, ?_⟩
    have heq : K ∩ ball (x : Phase) r = (K ∩ U) ∩ ball (x : Phase) r := by
      ext y
      simp only [mem_inter_iff]
      exact ⟨fun h => ⟨⟨h.1, hrU h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [heq]
    exact hc.inter (convex_ball _ _)
  choose r hr hc using hballs
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric
    (c := fun x : K => ball (x : Phase) (r x)) hA
    (fun x : K => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hAK hx⟩, mem_ball_self (hr _)⟩)
  refine ⟨δ, hδ, fun x hx => ?_⟩
  obtain ⟨z, hz⟩ := hcover x hx
  have heq : K ∩ ball x δ = (K ∩ ball (z : Phase) (r z)) ∩ ball x δ := by
    ext y
    simp only [mem_inter_iff]
    exact ⟨fun h => ⟨⟨h.1, hz h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  rw [heq]
  exact (hc z).inter (convex_ball _ _)
