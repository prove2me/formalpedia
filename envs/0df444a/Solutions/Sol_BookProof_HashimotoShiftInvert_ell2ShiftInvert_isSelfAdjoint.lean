-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.ell2ShiftInvert_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:39:22.658079+00:00
-- url     : https://prove2.me/submissions/b928bfa4-ead6-4cd6-a1c6-8669c8f85e9a

-- Generated from ChapterHashimotoShiftInvert.lean — solution of BookProof.HashimotoShiftInvert.ell2ShiftInvert_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Theorems.Thm_BookProof_HashimotoShiftInvert_diagCLM_isSelfAdjoint
open BookProof.HashimotoShiftInvert




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution : IsSelfAdjoint ell2ShiftInvert := diagCLM_isSelfAdjoint invCoeff_abs_le_one
