-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.resDist_le_chain
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:41:26.128399+00:00
-- url     : https://prove2.me/submissions/6d563713-6cf0-4228-8f7e-87f1e04599ad

import Definitions.Def_EdmondsKarp_ShortestPath_Run
import Theorems.Thm_EdmondsKarp_ShortestPath_pathArcs_chain
import Theorems.Thm_EdmondsKarp_ShortestPath_chain_simple

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (u v : V) (P : List V)
    (hh : P.head? = some u) (hl : P.getLast? = some v) (hc : P.IsChain (ResArc N f)) :
    resDist N f u v ≤ ((pathArcs P).length : ℕ∞) := by
  obtain ⟨Q, hnd, hchain, hhead, hlast, hlen⟩ := chain_simple (ResArc N f) P hc
  have hQ : IsDirPath N f u v Q :=
    ⟨hnd, hhead.trans hh, hlast.trans hl, (pathArcs_chain _ _).mpr hchain⟩
  have hdist : resDist N f u v ≤ ((pathArcs Q).length : ℕ∞) :=
    iInf_le_of_le Q (iInf_le_of_le hQ le_rfl)
  have hlength (L : List V) : (pathArcs L).length = L.length - 1 := by
    simp [pathArcs, Nat.min_eq_right (Nat.sub_le _ _)]
  refine hdist.trans ?_
  rw [hlength, hlength]
  exact_mod_cast Nat.sub_le_sub_right hlen 1
