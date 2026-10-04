-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.network_divergence
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:27:18.610514+00:00
-- url     : https://prove2.me/submissions/0402301d-8496-4349-8ae6-8501b0e0f2c8

import Definitions.Def_EdmondsKarp_ShortestPath_Network

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (g : V → V → ℝ) (u : V) :
    (∑ v ∈ Finset.univ.filter (fun v => (u, v) ∈ N.arcs), g u v) -
      (∑ v ∈ Finset.univ.filter (fun v => (v, u) ∈ N.arcs), g v u) =
    (∑ v : V, if (u, v) ∈ N.A then g u v else 0) -
      (∑ v : V, if (v, u) ∈ N.A then g v u else 0) +
    (if u = N.t then g N.t N.s else 0) - (if u = N.s then g N.t N.s else 0) := by
  have heq (x y : V) :
      (if (x, y) ∈ N.arcs then g x y else 0) =
      (if (x, y) ∈ N.A then g x y else 0) +
      (if x = N.t ∧ y = N.s then g N.t N.s else 0) := by
    by_cases h : x = N.t ∧ y = N.s
    · rcases h with ⟨rfl, rfl⟩
      simp [Network.arcs, N.return_not_mem]
    · simp [Network.arcs, Prod.mk.injEq, h]
  simp only [Finset.sum_filter]
  simp_rw [heq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hout : (∑ v : V, if u = N.t ∧ v = N.s then g N.t N.s else 0) =
      (if u = N.t then g N.t N.s else 0) := by
    by_cases h : u = N.t <;> simp [h]
  have hin : (∑ v : V, if v = N.t ∧ u = N.s then g N.t N.s else 0) =
      (if u = N.s then g N.t N.s else 0) := by
    by_cases h : u = N.s <;> simp [h]
  rw [hout, hin]
  ring
