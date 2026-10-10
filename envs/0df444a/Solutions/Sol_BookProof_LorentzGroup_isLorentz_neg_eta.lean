-- Prove2me | solution 1 for BookProof.LorentzGroup.isLorentz_neg_eta
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:43:42.440979+00:00
-- url     : https://prove2.me/submissions/2887f4d2-c8b5-4ca8-aa2f-b8bb53926da8

-- Generated from ChapterLorentzGroup.lean — solution of BookProof.LorentzGroup.isLorentz_neg_eta
import Mathlib
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : IsLorentz (-eta) := by

  ext i j; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, Fin.sum_univ_succ, eta ] ;
