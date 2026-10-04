-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.resDist_basics
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T20:04:20.906544+00:00
-- url     : https://prove2.me/submissions/3aa30c04-330d-4c5e-be5f-ff052c0fbd81

import Theorems.Thm_EdmondsKarp_ShortestPath_resDist_le_chain

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) :
    (∀ u : V, resDist N f u u = 0) ∧
    (∀ u v : V, ResArc N f u v → resDist N f u v ≤ 1) := by
  constructor
  · intro u
    apply le_antisymm _ zero_le
    simpa [pathArcs] using resDist_le_chain N f u u [u] (by simp) (by simp) (by simp)
  · intro u v h
    simpa [pathArcs] using resDist_le_chain N f u v [u, v] (by simp) (by simp)
      (by simpa [List.isChain_cons_cons] using h)
