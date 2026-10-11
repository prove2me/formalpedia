-- Prove2me | solution 1 for BookProof.ChapterPauliSU2.su2_preserves_time
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:04:51.458977+00:00
-- url     : https://prove2.me/submissions/a66507d6-e7e9-4102-adb4-59f36a02dd64

-- Generated from ChapterPauliSU2.lean — solution of BookProof.ChapterPauliSU2.su2_preserves_time
import Mathlib
import Definitions.Def_ChapterPauliSU2
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliSU2



open Matrix
open scoped BigOperators


open BookProof.ChapterPauliLorentz

set_option maxHeartbeats 1000000 in
theorem solution {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : Tᴴ * T = 1)
    (x : Fin 4 → ℝ) :
    (vecOfMat (spinorAction T (hermMat x))) 0 = x 0 := by

  unfold vecOfMat spinorAction hermMat;
  simp_all [ ← Matrix.ext_iff, Fin.forall_fin_two, Matrix.mul_apply ];
  norm_num [ Complex.ext_iff ] at *;
  grind
