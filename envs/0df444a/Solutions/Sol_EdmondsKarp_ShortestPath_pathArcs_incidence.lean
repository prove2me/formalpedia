-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.pathArcs_incidence
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:27:19.229387+00:00
-- url     : https://prove2.me/submissions/325837ad-e609-4127-b068-5305ae5bb990

import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (P : List V)
    (hP : P.Nodup) (u : V) (r : ℝ) :
    (∑ v : V, if (u, v) ∈ pathArcs P then r else 0) -
      (∑ v : V, if (v, u) ∈ pathArcs P then r else 0) =
    (if P.head? = some u then r else 0) - (if P.getLast? = some u then r else 0) := by
  induction P with
  | nil => simp [pathArcs]
  | cons a L ih =>
    cases L with
    | nil => simp [pathArcs]
    | cons b L =>
      have ha := (List.nodup_cons.mp hP).1
      have ht := (List.nodup_cons.mp hP).2
      have hs : pathArcs (a :: b :: L) = (a, b) :: pathArcs (b :: L) := rfl
      have hn : (a, b) ∉ pathArcs (b :: L) := by
        intro h
        exact ha (List.of_mem_zip h).1
      have hexpand (x y : V) :
          (if (x, y) ∈ pathArcs (a :: b :: L) then r else 0) =
          (if x = a ∧ y = b then r else 0) +
            (if (x, y) ∈ pathArcs (b :: L) then r else 0) := by
        by_cases hxy : x = a ∧ y = b
        · rcases hxy with ⟨rfl, rfl⟩
          simp [hs, hn]
        · simp [hs, Prod.mk.injEq, hxy]
      have hout : (∑ v : V, if u = a ∧ v = b then r else 0) =
          if u = a then r else 0 := by
        by_cases h : u = a <;> simp [h]
      have hin : (∑ v : V, if v = a ∧ u = b then r else 0) =
          if u = b then r else 0 := by
        by_cases h : u = b <;> simp [h]
      simp_rw [hexpand]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hout, hin]
      have hi := ih ht
      have heq (x : V) (xs : List V) : (if (x :: xs).head? = some u then r else 0) =
          (if u = x then r else 0) := by simp [eq_comm]
      rw [heq] at hi
      rw [heq, List.getLast?_cons_cons]
      linarith
