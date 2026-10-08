-- Prove2me | solution 1 for BookProof.ChapterPauliLorentz.sigma1sigma2_anti
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T09:06:42.359196+00:00
-- url     : https://prove2.me/submissions/ecd443db-5eec-4430-aeee-6e36396b8ae4

-- Generated from ChapterPauliLorentz.lean — solution of BookProof.ChapterPauliLorentz.sigma1sigma2_anti
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution : σ1 * σ2 + σ2 * σ1 = 0 := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ1, σ2]
