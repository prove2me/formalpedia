-- Prove2me | solution 1 for BunkbedAux.wzGraph_adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T01:33:27.439745+00:00
-- url     : https://prove2.me/submissions/fa7e30b1-2b76-4187-bd08-8735584389c1

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

private lemma mem_posts {V : Type*} [Fintype V] [DecidableEq V] (T : Finset V)
    (u v : V × Fin 2) :
    s(u, v) ∈ posts T ↔ u.1 = v.1 ∧ u.1 ∈ T ∧ u.2 ≠ v.2 := by
  obtain ⟨a, i⟩ := u; obtain ⟨b, j⟩ := v
  simp only [posts, mem_image, Sym2.eq_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, (⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ | ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩)⟩ <;> simp_all
  · rintro ⟨rfl, hT, hij⟩
    exact ⟨a, hT, by fin_cases i <;> fin_cases j <;> simp_all⟩

/-- **Adjacency in the Wierman-Ziff bunkbed graph.** Two vertices are adjacent exactly when some
hyperedge, on some level, contributes the edge joining them, or they are the two ends of a post
over the transversal set. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → (V × V × V)) (T : Finset V) (ψ : ι × Fin 2 → WZ) (u v : V × Fin 2) :
    (wzGraph t T ψ).Adj u v ↔
      ((∃ p : ι × Fin 2, s(u, v) ∈ (ψ p).edges (t p.1) p.2)
        ∨ (u.1 = v.1 ∧ u.1 ∈ T ∧ u.2 ≠ v.2)) ∧ u ≠ v := by
  rw [wzGraph, ofEdges, fromEdgeSet_adj]
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, mem_biUnion,
    Finset.mem_univ, true_and, mem_posts]
