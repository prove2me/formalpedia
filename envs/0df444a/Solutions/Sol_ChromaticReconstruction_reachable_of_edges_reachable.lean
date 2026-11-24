-- Prove2me | solution 1 for ChromaticReconstruction.reachable_of_edges_reachable
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T20:52:15.818036+00:00
-- url     : https://prove2.me/submissions/75f8aad9-ea83-4827-8edb-712d289f6c13

import Mathlib

open SimpleGraph

theorem solution {V : Type*} {A B : Set (Sym2 V)}
    (h : ∀ u v, s(u, v) ∈ A → (SimpleGraph.fromEdgeSet B).Reachable u v) {x y : V}
    (hxy : (SimpleGraph.fromEdgeSet A).Reachable x y) :
    (SimpleGraph.fromEdgeSet B).Reachable x y := by
  obtain ⟨w⟩ := hxy
  induction w with
  | nil => exact Reachable.rfl
  | cons hadj p ih =>
    simp only [fromEdgeSet_adj] at hadj
    exact Reachable.trans (h _ _ hadj.1) ih