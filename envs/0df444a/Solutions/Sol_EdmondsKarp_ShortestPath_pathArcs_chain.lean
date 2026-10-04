-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.pathArcs_chain
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:35:58.115469+00:00
-- url     : https://prove2.me/submissions/9215779e-3d12-4580-adf3-9100b710de59

import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (R : V → V → Prop) (P : List V) :
    (∀ e ∈ pathArcs P, R e.1 e.2) ↔ P.IsChain R := by
  induction P with
  | nil => simp [pathArcs]
  | cons a L ih =>
    cases L with
    | nil => simp [pathArcs]
    | cons b L =>
      have hs : pathArcs (a :: b :: L) = (a, b) :: pathArcs (b :: L) := rfl
      rw [hs]
      simp only [List.forall_mem_cons, List.isChain_cons_cons, ih]
