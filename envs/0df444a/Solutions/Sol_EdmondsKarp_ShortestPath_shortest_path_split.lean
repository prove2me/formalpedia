-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.shortest_path_split
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T20:09:53.47499+00:00
-- url     : https://prove2.me/submissions/d263e8f2-affc-4934-b35c-f3fcadb131a1

import Theorems.Thm_EdmondsKarp_ShortestPath_resDist_triangle
import Theorems.Thm_EdmondsKarp_ShortestPath_resDist_shortest
import Theorems.Thm_EdmondsKarp_ShortestPath_pathArcs_chain
import Theorems.Thm_EdmondsKarp_ShortestPath_resDist_le_chain

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hP : IsShortestAugPath N f P)
    (L R : List V) (u : V) (he : P = L ++ u :: R) :
    resDist N f N.s u = (L.length : ℕ∞) ∧ resDist N f u N.t = (R.length : ℕ∞) := by
  subst P
  have hc := (pathArcs_chain _ _).mp hP.1.2.2.2
  obtain ⟨hcL, hcR⟩ := List.isChain_split.mp hc
  have hh : (L ++ [u]).head? = some N.s := by
    cases L <;> simpa using hP.1.2.1
  have hl : (u :: R).getLast? = some N.t := by simpa using hP.1.2.2.1
  have hdL := resDist_le_chain N f N.s u (L ++ [u]) hh (by simp) hcL
  have hdR := resDist_le_chain N f u N.t (u :: R) (by simp) hl hcR
  have hlength (M : List V) : (pathArcs M).length = M.length - 1 := by simp [pathArcs]
  simp only [hlength, List.length_append, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.add_zero, Nat.add_sub_cancel] at hdL hdR
  have htri := resDist_triangle N f N.s u N.t
  rw [(resDist_shortest N f (L ++ u :: R) hP).1] at htri
  simp only [hlength, List.length_append, List.length_cons] at htri
  have htotal : L.length + (R.length + 1) - 1 = L.length + R.length := by omega
  rw [htotal, Nat.cast_add] at htri
  generalize resDist N f N.s u = x at hdL htri ⊢
  generalize resDist N f u N.t = y at hdR htri ⊢
  enat_to_nat <;> omega
