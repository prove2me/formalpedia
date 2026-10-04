-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.resDist_monotone
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T20:09:51.174138+00:00
-- url     : https://prove2.me/submissions/801b6aa7-40d5-4471-a11a-b83bac9d766c

import Theorems.Thm_EdmondsKarp_ShortestPath_residual_next_sub
import Theorems.Thm_EdmondsKarp_ShortestPath_shortest_path_arc_distances
import Theorems.Thm_EdmondsKarp_ShortestPath_resDist_basics
import Theorems.Thm_EdmondsKarp_ShortestPath_path_potential_bound
import Theorems.Thm_EdmondsKarp_ShortestPath_resDist_triangle
import Theorems.Thm_EdmondsKarp_ShortestPath_pathArcs_chain

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P)
    (k : ℕ) (hk : k < K) (u : V) :
    resDist N (f k) N.s u ≤ resDist N (f (k + 1)) N.s u ∧
    resDist N (f k) u N.t ≤ resDist N (f (k + 1)) u N.t := by
  have haux (x : ℕ∞) : x ≤ x + 1 + 1 := by enat_to_nat <;> omega
  have hforward : ∀ x y, ResArc N (f (k + 1)) x y →
      resDist N (f k) N.s y ≤ resDist N (f k) N.s x + 1 := by
    intro x y h
    rcases residual_next_sub N K f P hrun k hk x y h with h | h
    · exact (resDist_triangle N (f k) N.s x y).trans
        (add_le_add le_rfl ((resDist_basics N (f k)).2 x y h))
    · rw [(shortest_path_arc_distances N (f k) (P k) (hrun.2 k hk).1 y x h).1]
      exact haux _
  have hbackward : ∀ x y, ResArc N (f (k + 1)) x y →
      resDist N (f k) x N.t ≤ resDist N (f k) y N.t + 1 := by
    intro x y h
    rcases residual_next_sub N K f P hrun k hk x y h with h | h
    · have he := (resDist_triangle N (f k) x y N.t).trans
        (add_le_add ((resDist_basics N (f k)).2 x y h) le_rfl)
      simpa [add_comm] using he
    · rw [(shortest_path_arc_distances N (f k) (P k) (hrun.2 k hk).1 y x h).2.1]
      exact haux _
  constructor
  · refine le_iInf fun Q => le_iInf fun hQ => ?_
    have hb := path_potential_bound (ResArc N (f (k + 1))) (resDist N (f k) N.s)
      hforward Q N.s u hQ.2.1 hQ.2.2.1 ((pathArcs_chain _ _).mp hQ.2.2.2)
    simpa [(resDist_basics N (f k)).1 N.s] using hb
  · refine le_iInf fun Q => le_iInf fun hQ => ?_
    have hc := (pathArcs_chain _ _).mp hQ.2.2.2
    have hb := path_potential_bound (fun x y => ResArc N (f (k + 1)) y x)
      (fun x => resDist N (f k) x N.t) (fun x y h => hbackward y x h)
      Q.reverse N.t u (by simpa using hQ.2.2.1) (by simpa using hQ.2.1)
      (List.isChain_reverse.mpr hc)
    have hlen : (pathArcs Q.reverse).length = (pathArcs Q).length := by simp [pathArcs]
    simpa [(resDist_basics N (f k)).1 N.t, hlen] using hb
