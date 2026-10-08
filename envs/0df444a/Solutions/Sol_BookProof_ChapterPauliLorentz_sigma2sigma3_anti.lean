-- Prove2me | solution 1 for BookProof.ChapterPauliLorentz.sigma2sigma3_anti
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T09:06:54.341703+00:00
-- url     : https://prove2.me/submissions/7f90670b-f43c-45d7-8555-c7ef196c7311

-- Generated from ChapterPauliLorentz.lean — solution of BookProof.ChapterPauliLorentz.sigma2sigma3_anti
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution : σ2 * σ3 + σ3 * σ2 = 0 := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ2, σ3]
