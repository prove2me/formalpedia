-- Prove2me | solution 1 for BookProof.LorentzGroup.eta_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:41:36.767461+00:00
-- url     : https://prove2.me/submissions/a980223e-a3e0-4671-bf4b-0933c5608e3a

-- Generated from ChapterLorentzGroup.lean — solution of BookProof.LorentzGroup.eta_mul_self
import Mathlib
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : eta * eta = 1 := by

  ext i j; fin_cases i <;> fin_cases j <;> simp [ eta, Matrix.mul_apply ] ;
  all_goals norm_num [ Fin.sum_univ_succ, Fin.sum_univ_zero ] ;
