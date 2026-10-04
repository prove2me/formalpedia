-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.pathArcs_simple
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:27:20.110269+00:00
-- url     : https://prove2.me/submissions/676e3ca6-4c80-4f3f-abc7-8cce546094ed

import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (P : List V)
    (hP : P.Nodup) (u v : V) (h : (u, v) ∈ pathArcs P) :
    u ≠ v ∧ (v, u) ∉ pathArcs P ∧ P.head? ≠ some v ∧ P.getLast? ≠ some u := by
  induction P with
  | nil => simp [pathArcs] at h
  | cons a L ih =>
    cases L with
    | nil => simp [pathArcs] at h
    | cons b L =>
      have ha := (List.nodup_cons.mp hP).1
      have ht := (List.nodup_cons.mp hP).2
      have hab : a ≠ b := by intro e; exact ha (by simp [e])
      have hs : pathArcs (a :: b :: L) = (a, b) :: pathArcs (b :: L) := rfl
      rw [hs, List.mem_cons] at h
      rcases h with h | h
      · cases Prod.mk.inj h with
        | intro hu hv =>
          subst u; subst v
          refine ⟨hab, ?_, ?_, ?_⟩
          · rw [hs, List.mem_cons]
            rintro (he | he)
            · exact hab (Prod.mk.inj he).1.symm
            · exact ha (List.mem_of_mem_tail (List.of_mem_zip he).2)
          · simpa using hab
          · rw [List.getLast?_cons_cons]
            intro he
            exact ha (List.mem_of_getLast? he)
      · obtain ⟨hne, hrev, hhead, hlast⟩ := ih ht h
        have hu := (List.of_mem_zip h).1
        have hv := List.mem_of_mem_tail (List.of_mem_zip h).2
        refine ⟨hne, ?_, ?_, ?_⟩
        · rw [hs, List.mem_cons]
          rintro (he | he)
          · exact ha ((Prod.mk.inj he).1 ▸ hv)
          · exact hrev he
        · intro he
          exact ha ((Option.some.inj he).symm ▸ hv)
        · simpa only [List.getLast?_cons_cons] using hlast
