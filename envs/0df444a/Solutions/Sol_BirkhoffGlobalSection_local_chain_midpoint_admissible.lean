-- Prove2me | solution 1 for BirkhoffGlobalSection.local_chain_midpoint_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:40:01.540511+00:00
-- url     : https://prove2.me/submissions/7dd86d60-ae7e-46c8-9a98-52785aaf8034

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

theorem solution (K B : Set Phase) (hB : Convex ℝ B)
    (a b c : Phase) (ha : a ∈ K ∩ B) (hc : c ∈ K ∩ B)
    (δ ε : ℝ) (hεδ : ε < δ)
    (hlab : dist a b ≤ ε) (hrbc : dist b c ≤ ε)
    (hloc : Convex ℝ (K ∩ ball b δ)) :
    (1 / 2 : ℝ) • (a + c) ∈ K ∩ B ∧
      dist a ((1 / 2 : ℝ) • (a + c)) ≤ ε ∧
      dist ((1 / 2 : ℝ) • (a + c)) c ≤ ε := by
  have ha' : a ∈ K ∩ ball b δ := ⟨ha.1, hlab.trans_lt hεδ⟩
  have hc' : c ∈ K ∩ ball b δ := ⟨hc.1, by
    rw [mem_ball, dist_comm]
    exact hrbc.trans_lt hεδ⟩
  have hmK := (hloc.midpoint_mem ha' hc').1
  have hmB := hB.midpoint_mem ha.2 hc.2
  have htri := dist_triangle a b c
  have hl : dist a (midpoint ℝ a c) = (1 / 2 : ℝ) * dist a c := by
    norm_num [dist_left_midpoint]
  have hr : dist (midpoint ℝ a c) c = (1 / 2 : ℝ) * dist a c := by
    norm_num [dist_midpoint_right]
  have hmid : midpoint ℝ a c = (1 / 2 : ℝ) • (a + c) := by
    simp [midpoint_eq_smul_add]
  rw [hmid] at hmK hmB hl hr
  refine ⟨⟨hmK, hmB⟩, ?_, ?_⟩ <;> linarith
