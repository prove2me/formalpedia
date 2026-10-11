-- Prove2me | solution 1 for BookProof.ChapterPauliSU2.spinorAction_neg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:04:48.309772+00:00
-- url     : https://prove2.me/submissions/ce610dfd-903f-42c7-86ec-10ba9c9e96cf

-- Generated from ChapterPauliSU2.lean — solution of BookProof.ChapterPauliSU2.spinorAction_neg
import Mathlib
import Definitions.Def_ChapterPauliSU2
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliSU2



open Matrix
open scoped BigOperators


open BookProof.ChapterPauliLorentz

set_option maxHeartbeats 1000000 in
theorem solution (T X : Matrix (Fin 2) (Fin 2) ℂ) :
    spinorAction (-T) X = spinorAction T X := by

  unfold spinorAction; simp [ Matrix.conjTranspose_neg ] ;
