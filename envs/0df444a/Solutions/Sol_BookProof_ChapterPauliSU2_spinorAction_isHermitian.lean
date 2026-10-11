-- Prove2me | solution 1 for BookProof.ChapterPauliSU2.spinorAction_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:04:49.289674+00:00
-- url     : https://prove2.me/submissions/6f70abfa-5832-43b4-b961-98945674f66c

-- Generated from ChapterPauliSU2.lean — solution of BookProof.ChapterPauliSU2.spinorAction_isHermitian
import Mathlib
import Definitions.Def_ChapterPauliSU2
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliSU2



open Matrix
open scoped BigOperators


open BookProof.ChapterPauliLorentz

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ)
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : Xᴴ = X) :
    (spinorAction T X)ᴴ = spinorAction T X := by

  unfold spinorAction;
  simp [ hX, Matrix.mul_assoc ]
