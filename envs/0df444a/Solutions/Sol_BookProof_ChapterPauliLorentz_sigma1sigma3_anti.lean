-- Prove2me | solution 1 for BookProof.ChapterPauliLorentz.sigma1sigma3_anti
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T09:07:06.086073+00:00
-- url     : https://prove2.me/submissions/15edbd0f-150d-48f6-a05a-07725719fae7

-- Generated from ChapterPauliLorentz.lean — solution of BookProof.ChapterPauliLorentz.sigma1sigma3_anti
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution : σ1 * σ3 + σ3 * σ1 = 0 := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ1, σ3]
