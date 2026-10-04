-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.resDist_shortest
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T20:04:21.834355+00:00
-- url     : https://prove2.me/submissions/353a781b-23b5-460d-aa69-364b611e7f65

import Definitions.Def_EdmondsKarp_ShortestPath_Run

open EdmondsKarp.ShortestPath

theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hP : IsShortestAugPath N f P) :
    resDist N f N.s N.t = ((pathArcs P).length : ℕ∞) ∧
    1 ≤ (pathArcs P).length ∧ (pathArcs P).length < Fintype.card V := by
  have hlen : (pathArcs P).length = P.length - 1 := by simp [pathArcs]
  have hlong : 2 ≤ P.length := by
    cases P with
    | nil => simp [IsShortestAugPath, IsAugPath, IsDirPath] at hP
    | cons a T =>
      cases T with
      | nil =>
        have hs : a = N.s := by simpa using hP.1.2.1
        have ht : a = N.t := by simpa using hP.1.2.2.1
        exact (N.source_ne_sink (hs.symm.trans ht)).elim
      | cons b T => simp
  refine ⟨?_, ?_, ?_⟩
  · apply le_antisymm (iInf_le_of_le P (iInf_le_of_le hP.1 le_rfl))
    refine le_iInf fun Q => le_iInf fun hQ => ?_
    exact_mod_cast hP.2 Q hQ
  · omega
  · have hcard := hP.1.1.length_le_card
    omega
