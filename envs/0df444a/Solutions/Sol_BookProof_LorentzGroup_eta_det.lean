-- Prove2me | solution 1 for BookProof.LorentzGroup.eta_det
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:41:59.820997+00:00
-- url     : https://prove2.me/submissions/71581c16-d3d8-43c3-b0b4-715fcb7f90ba

-- Generated from ChapterLorentzGroup.lean — solution of BookProof.LorentzGroup.eta_det
import Mathlib
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzGroup




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : eta.det = -1 := by

  norm_num [ Matrix.det_succ_row_zero, eta ];
  simp [ Fin.sum_univ_succ ]
