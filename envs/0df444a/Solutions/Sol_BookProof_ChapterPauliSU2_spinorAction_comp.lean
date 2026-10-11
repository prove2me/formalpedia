-- Prove2me | solution 1 for BookProof.ChapterPauliSU2.spinorAction_comp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:04:47.135271+00:00
-- url     : https://prove2.me/submissions/c4338c48-3188-4499-b461-5eadff297299

-- Generated from ChapterPauliSU2.lean — solution of BookProof.ChapterPauliSU2.spinorAction_comp
import Mathlib
import Definitions.Def_ChapterPauliSU2
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliSU2



open Matrix
open scoped BigOperators


open BookProof.ChapterPauliLorentz

set_option maxHeartbeats 1000000 in
theorem solution (T₁ T₂ X : Matrix (Fin 2) (Fin 2) ℂ) :
    spinorAction (T₁ * T₂) X = spinorAction T₂ (spinorAction T₁ X) := by

  unfold spinorAction; rw [ Matrix.conjTranspose_mul ] ; simp [ Matrix.mul_assoc ] ;
