-- Prove2me | solution 1 for BookProof.ChapterH8.inv_comp_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T03:16:48.881442+00:00
-- url     : https://prove2.me/submissions/c008c615-031a-46dc-ac90-8371abb412af

import Mathlib
import Definitions.Def_ChapterH8

set_option autoImplicit false

open BookProof.ChapterH8 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6 in
theorem solution {F G : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    {A : F →L[ℂ] F} {B : G →L[ℂ] G} {Ai : F →L[ℂ] F} {Bi : G →L[ℂ] G}
    (P : G →L[ℂ] F) (hAl : Ai.comp A = ContinuousLinearMap.id ℂ F)
    (hBr : B.comp Bi = ContinuousLinearMap.id ℂ G)
    (hPB : P.comp B = A.comp P) :
    P.comp Bi = Ai.comp P := by
  calc P.comp Bi = (Ai.comp A).comp (P.comp Bi) := by
        rw [hAl]; rfl
    _ = Ai.comp ((A.comp P).comp Bi) := by
        simp only [ContinuousLinearMap.comp_assoc]
    _ = Ai.comp ((P.comp B).comp Bi) := by rw [hPB]
    _ = Ai.comp (P.comp (B.comp Bi)) := by
        simp only [ContinuousLinearMap.comp_assoc]
    _ = Ai.comp P := by rw [hBr]; rfl
