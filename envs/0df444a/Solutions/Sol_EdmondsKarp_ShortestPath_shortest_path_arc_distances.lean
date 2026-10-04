-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.shortest_path_arc_distances
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T20:09:52.690014+00:00
-- url     : https://prove2.me/submissions/66b55f66-5cc9-4277-9d35-09e4375fcb61

import Theorems.Thm_EdmondsKarp_ShortestPath_shortest_path_split
import Theorems.Thm_EdmondsKarp_ShortestPath_pathArcs_split
import Theorems.Thm_EdmondsKarp_ShortestPath_resDist_shortest

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hP : IsShortestAugPath N f P)
    (u v : V) (he : (u, v) ∈ pathArcs P) :
    resDist N f N.s v = resDist N f N.s u + 1 ∧
    resDist N f u N.t = resDist N f v N.t + 1 ∧
    resDist N f N.s N.t = resDist N f N.s u + 1 + resDist N f v N.t := by
  obtain ⟨L, R, rfl⟩ := pathArcs_split P u v he
  have hu := shortest_path_split N f (L ++ u :: v :: R) hP L (v :: R) u rfl
  have hv := shortest_path_split N f (L ++ u :: v :: R) hP (L ++ [u]) R v (by simp)
  refine ⟨?_, ?_, ?_⟩
  · rw [hv.1, hu.1]
    simp
  · rw [hu.2, hv.2]
    simp
  · rw [(resDist_shortest N f (L ++ u :: v :: R) hP).1, hu.1, hv.2]
    have hlen : (pathArcs (L ++ u :: v :: R)).length = L.length + 1 + R.length := by
      simp [pathArcs]
      omega
    rw [hlen]
    simp
