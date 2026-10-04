-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.resDist_add_two_of_reversed
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T20:16:05.210257+00:00
-- url     : https://prove2.me/submissions/b9896fa7-b5e4-414e-b94d-0013a0bb1dee

import Theorems.Thm_EdmondsKarp_ShortestPath_resDist_monotone_run
import Theorems.Thm_EdmondsKarp_ShortestPath_shortest_path_arc_distances

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P)
    (k l : ℕ) (hkl : k < l) (hl : l < K) (u v : V)
    (huv : (u, v) ∈ pathArcs (P k)) (hvu : (v, u) ∈ pathArcs (P l)) :
    resDist N (f k) N.s N.t + 2 ≤ resDist N (f l) N.s N.t := by
  have hk : k < K := by omega
  have hfirst := shortest_path_arc_distances N (f k) (P k) (hrun.2 k hk).1 u v huv
  have hlast := shortest_path_arc_distances N (f l) (P l) (hrun.2 l hl).1 v u hvu
  have hleft : resDist N (f k) N.s u + 1 ≤ resDist N (f l) N.s v := by
    rw [← hfirst.1]
    exact (resDist_monotone_run N K f P hrun k l hkl.le hl.le v).1
  have hright : resDist N (f k) v N.t + 1 ≤ resDist N (f l) u N.t := by
    rw [← hfirst.2.1]
    exact (resDist_monotone_run N K f P hrun k l hkl.le hl.le u).2
  rw [hfirst.2.2, hlast.2.2]
  calc
    resDist N (f k) N.s u + 1 + resDist N (f k) v N.t + 2 =
      (resDist N (f k) N.s u + 1) + 1 + (resDist N (f k) v N.t + 1) := by
        rw [show (2 : ℕ∞) = 1 + 1 by rfl]
        ac_rfl
    _ ≤ resDist N (f l) N.s v + 1 + resDist N (f l) u N.t :=
      add_le_add (add_le_add hleft le_rfl) hright
