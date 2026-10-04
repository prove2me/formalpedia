-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.pathArcs_split
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T20:04:20.090809+00:00
-- url     : https://prove2.me/submissions/bd98db0e-6149-4e71-8d4a-b10afb4c7082

import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (P : List V)
    (u v : V) (h : (u, v) ∈ pathArcs P) : ∃ L R, P = L ++ u :: v :: R := by
  induction P with
  | nil => simp [pathArcs] at h
  | cons a T ih =>
    cases T with
    | nil => simp [pathArcs] at h
    | cons b T =>
      have hs : pathArcs (a :: b :: T) = (a, b) :: pathArcs (b :: T) := rfl
      rw [hs, List.mem_cons] at h
      rcases h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨[], T, rfl⟩
      · obtain ⟨L, R, he⟩ := ih h
        exact ⟨a :: L, R, by simp [he]⟩
