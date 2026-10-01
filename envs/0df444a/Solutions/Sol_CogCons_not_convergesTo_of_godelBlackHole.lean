-- Prove2me | solution 1 for CogCons.not_convergesTo_of_godelBlackHole
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T20:01:34.686706+00:00
-- url     : https://prove2.me/submissions/4672c258-5ccb-49af-8814-03349550bdba

import Definitions.Def_CogCons_similarity_distance

open CogCons CogCons.CognitiveSimilarityDistance

theorem solution {C : Type*} (D : CognitiveSimilarityDistance C)
    (A : Set C) (s : ℕ → C) (x : C) (h : D.IsGodelBlackHole A s x) :
    ¬ D.ConvergesTo s x := by
  obtain ⟨ε, hε, k, hk, _⟩ := h
  intro hs
  obtain ⟨m, hm⟩ := hs ε hε
  exact hk (max k m) (le_max_left _ _) (hm (max k m) (le_max_right _ _))
