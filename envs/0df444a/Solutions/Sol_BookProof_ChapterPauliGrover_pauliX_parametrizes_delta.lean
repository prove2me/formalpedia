-- Prove2me | solution 1 for BookProof.ChapterPauliGrover.pauliX_parametrizes_delta
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:04:27.459441+00:00
-- url     : https://prove2.me/submissions/ba11bc21-1fe1-478f-9fe0-ae648f20f8a9

-- Generated from ChapterPauliGrover.lean — solution of BookProof.ChapterPauliGrover.pauliX_parametrizes_delta
import Mathlib
import Definitions.Def_ChapterPauliGrover
import Definitions.Def_ChapterConditional
open BookProof.ChapterPauliGrover



open scoped BigOperators Matrix ComplexConjugate
open Matrix
open BookProof.ChapterConditional

set_option maxHeartbeats 1000000 in
theorem solution (y : Fin 2) :
    ‖pauliX y 0‖ ^ 2 = (if y = 1 then 1 else 0 : ℝ) := by

  fin_cases y <;> simp [pauliX]
