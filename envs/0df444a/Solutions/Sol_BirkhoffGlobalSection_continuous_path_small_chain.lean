-- Prove2me | solution 1 for BirkhoffGlobalSection.continuous_path_small_chain
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:40:00.677231+00:00
-- url     : https://prove2.me/submissions/23da37df-b745-486e-befb-145af824d73e

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

theorem solution (C : Set Phase) (γ : I → Phase)
    (hγ : Continuous γ) (hC : ∀ t, γ t ∈ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ p : Fin (N + 1) → Phase,
      p 0 = γ 0 ∧ p (Fin.last N) = γ 1 ∧
      (∀ i, p i ∈ C) ∧ (∀ i : Fin N, dist (p i.castSucc) (p i.succ) < ε) := by
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, htcover⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun u : I => γ ⁻¹' ball (γ u) (ε / 2))
      (fun u => isOpen_ball.preimage hγ) (by
        intro u _
        exact mem_iUnion.mpr ⟨u, mem_ball_self (by linarith)⟩)
  let N := m + 1
  let p : Fin (N + 1) → Phase := fun i => γ (t i.val)
  refine ⟨N, by omega, p, ?_, ?_, fun i => hC _, ?_⟩
  · change γ (t 0) = γ 0
    rw [ht0]
  · change γ (t N) = γ 1
    rw [hm N (by dsimp [N]; omega)]
  · intro i
    obtain ⟨u, hu⟩ := htcover i.val
    have hleft := hu (left_mem_Icc.mpr (htmono (Nat.le_succ i.val)))
    have hright := hu (right_mem_Icc.mpr (htmono (Nat.le_succ i.val)))
    have hl : dist (γ (t i.val)) (γ u) < ε / 2 := hleft
    have hr : dist (γ (t (i.val + 1))) (γ u) < ε / 2 := hright
    change dist (γ (t i.val)) (γ (t (i.val + 1))) < ε
    have htri := dist_triangle (γ (t i.val)) (γ u) (γ (t (i.val + 1)))
    rw [dist_comm (γ u)] at htri
    linarith
