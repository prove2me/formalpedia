-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.resDist_triangle
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T20:09:51.933362+00:00
-- url     : https://prove2.me/submissions/48d7c6b4-7854-46d7-bdd5-55482b0853d5

import Theorems.Thm_EdmondsKarp_ShortestPath_resDist_le_chain
import Theorems.Thm_EdmondsKarp_ShortestPath_pathArcs_chain

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (a b c : V) :
    resDist N f a c ≤ resDist N f a b + resDist N f b c := by
  conv_rhs => unfold resDist
  simp_rw [ENat.iInf_add, ENat.add_iInf]
  refine le_iInf fun P => le_iInf fun hP => le_iInf fun Q => le_iInf fun hQ => ?_
  have hnP : P ≠ [] := by intro he; simpa [he] using hP.2.1
  have hcP := (pathArcs_chain _ _).mp hP.2.2.2
  have hcQ := (pathArcs_chain _ _).mp hQ.2.2.2
  cases Q with
  | nil => simp [IsDirPath] at hQ
  | cons v L =>
    have hv : v = b := by simpa using hQ.2.1
    subst v
    have hc : (P ++ L).IsChain (ResArc N f) := by
      apply hcP.append hcQ.tail
      intro x hx y hy
      have hx' : x = b := by simpa [hP.2.2.1, eq_comm] using hx
      subst x
      exact hcQ.rel_head? hy
    have hh : (P ++ L).head? = some a := by
      rw [List.head?_append_of_ne_nil _ hnP]
      exact hP.2.1
    have hl : (P ++ L).getLast? = some c := by
      cases L with
      | nil => simpa [hP.2.2.1] using hQ.2.2.1
      | cons v L => simpa using hQ.2.2.1
    have hbound := resDist_le_chain N f a c (P ++ L) hh hl hc
    have hlength (M : List V) : (pathArcs M).length = M.length - 1 := by
      simp [pathArcs, Nat.min_eq_right (Nat.sub_le _ _)]
    have hlen : (pathArcs (P ++ L)).length = (pathArcs P).length +
        (pathArcs (b :: L)).length := by
      simp only [hlength, List.length_append, List.length_cons]
      have : 0 < P.length := List.length_pos_iff.mpr hnP
      omega
    simpa only [hlen, Nat.cast_add] using hbound
