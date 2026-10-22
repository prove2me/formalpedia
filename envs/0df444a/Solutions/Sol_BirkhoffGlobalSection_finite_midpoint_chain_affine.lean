-- Prove2me | solution 1 for BirkhoffGlobalSection.finite_midpoint_chain_affine
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:40:02.909399+00:00
-- url     : https://prove2.me/submissions/36fccdb0-9acf-4837-b278-2624fd7d96cf

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

theorem solution (N : ℕ) (hN : 0 < N) (p : Fin (N + 1) → Phase)
    (hmid : ∀ i j : Fin N, j.succ = i.castSucc →
      p i.castSucc = (1 / 2 : ℝ) • (p j.castSucc + p i.succ)) :
    ∃ d : Phase, ∀ k : Fin (N + 1), p k = p 0 + (k.val : ℝ) • d := by
  let d := p ⟨1, by omega⟩ - p 0
  have hd : ∀ n (hn : n < N),
      p ⟨n + 1, by omega⟩ - p ⟨n, by omega⟩ = d := by
    intro n
    induction n with
    | zero =>
      intro hn
      rfl
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hm := hmid ⟨n + 1, hn⟩ ⟨n, by omega⟩ (Fin.ext rfl)
      ext l
      have hi' := congrFun hi l
      have hm' := congrFun hm l
      change p ⟨n + 1, by omega⟩ l =
        (1 / 2 : ℝ) * (p ⟨n, by omega⟩ l + p ⟨n + 1 + 1, by omega⟩ l) at hm'
      simp only [Pi.sub_apply] at hi' ⊢
      nlinarith
  have haff : ∀ n (hn : n ≤ N), p ⟨n, by omega⟩ = p 0 + (n : ℝ) • d := by
    intro n
    induction n with
    | zero =>
      intro hn
      simp
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hh := hd n (by omega)
      ext l
      have hi' := congrFun hi l
      have hh' := congrFun hh l
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
        Nat.cast_add, Nat.cast_one] at hi' hh' ⊢
      nlinarith
  exact ⟨d, fun k => haff k.val (by omega)⟩
