-- Prove2me | solution 1 for BirkhoffGlobalSection.affine_chain_convex_combinations_mem
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:40:03.552988+00:00
-- url     : https://prove2.me/submissions/4540f7bc-743a-457b-bf7f-37563aa5bb9d

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

theorem solution (K : Set Phase) (N : ℕ) (hN : 0 < N)
    (p : Fin (N + 1) → Phase) (d : Phase)
    (haff : ∀ k, p k = p 0 + (k.val : ℝ) • d)
    (hpmem : ∀ k, p k ∈ K) (δ ε : ℝ) (hδ : 0 < δ) (hεδ : ε < δ)
    (hedge : ∀ i : Fin N, dist (p i.castSucc) (p i.succ) ≤ ε)
    (hloc : ∀ k, Convex ℝ (K ∩ ball (p k) δ))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • p 0 + b • p (Fin.last N) ∈ K := by
  by_cases hb1 : b = 1
  · have ha0 : a = 0 := by linarith
    simpa only [ha0, hb1, zero_smul, one_smul, zero_add] using hpmem (Fin.last N)
  have hble : b ≤ 1 := by linarith
  have hblt : b < 1 := lt_of_le_of_ne hble hb1
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hbN : 0 ≤ b * (N : ℝ) := mul_nonneg hb hNR.le
  let n := Nat.floor (b * (N : ℝ))
  have hn : n < N := (Nat.floor_lt hbN).mpr (by nlinarith)
  let i : Fin N := ⟨n, hn⟩
  let t : ℝ := b * (N : ℝ) - n
  have ht0 : 0 ≤ t := sub_nonneg.mpr (Nat.floor_le hbN)
  have ht1 : t ≤ 1 := by
    have hh := Nat.lt_floor_add_one (b * (N : ℝ))
    dsimp [t, n]
    linarith
  have hleft : p i.castSucc ∈ K ∩ ball (p i.castSucc) δ :=
    ⟨hpmem _, mem_ball_self hδ⟩
  have hright : p i.succ ∈ K ∩ ball (p i.castSucc) δ := by
    refine ⟨hpmem _, ?_⟩
    rw [mem_ball, dist_comm]
    exact (hedge i).trans_lt hεδ
  have hmem := (hloc i.castSucc) hleft hright (sub_nonneg.mpr ht1) ht0
    (show (1 - t) + t = 1 by ring)
  have heq : a • p 0 + b • p (Fin.last N) =
      (1 - t) • p i.castSucc + t • p i.succ := by
    rw [haff (Fin.last N), haff i.castSucc, haff i.succ]
    ext l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Fin.val_last, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    have haeq : a = 1 - b := by linarith
    rw [haeq]
    dsimp [t, i]
    ring
  rw [heq]
  exact hmem.1
