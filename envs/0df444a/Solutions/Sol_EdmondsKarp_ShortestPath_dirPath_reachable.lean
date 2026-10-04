-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.dirPath_reachable
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:35:56.803293+00:00
-- url     : https://prove2.me/submissions/4aed06d7-118c-4aed-a72d-792f87884e86

import Theorems.Thm_EdmondsKarp_ShortestPath_pathArcs_chain
import Theorems.Thm_EdmondsKarp_ShortestPath_chain_simple

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (u v : V) :
    (∃ P, IsDirPath N f u v P) ↔ Relation.ReflTransGen (ResArc N f) u v := by
  constructor
  · rintro ⟨P, hnd, hh, hl, hc⟩
    have hne : P ≠ [] := by intro h; simp [h] at hh
    have hh' : P.head hne = u := by simpa [List.head?_eq_some_head hne] using hh
    have hl' : P.getLast hne = v := by simpa [List.getLast?_eq_some_getLast hne] using hl
    simpa [hh', hl'] using
      List.relationReflTransGen_of_exists_isChain P ((pathArcs_chain _ _).mp hc) hne
  · intro h
    obtain ⟨P, hne, hc, hh, hl⟩ := List.exists_isChain_ne_nil_of_relationReflTransGen h
    obtain ⟨Q, hnd, hchain, hhead, hlast, _⟩ := chain_simple (ResArc N f) P hc
    refine ⟨Q, hnd, ?_, ?_, (pathArcs_chain _ _).mpr hchain⟩
    · rw [hhead, List.head?_eq_some_head hne, hh]
    · rw [hlast, List.getLast?_eq_some_getLast hne, hl]
