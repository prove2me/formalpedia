-- Prove2me | solution 1 for BookProof.ChapterDoubleSlit.Hpsi0
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:25:03.733185+00:00
-- url     : https://prove2.me/submissions/95071c98-9cf4-46c0-a6d7-b9e0371b4eda

-- Generated from ChapterDoubleSlit.lean — solution of BookProof.ChapterDoubleSlit.Hpsi0
import Mathlib
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution : H *ᵥ psi0 = fun _ => (1 / Real.sqrt 2 : ℂ) := by

  funext i
  fin_cases i <;>
    simp [H, psi0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply]
