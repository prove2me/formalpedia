-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_canonical
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T14:49:31.478317+00:00
-- url     : https://prove2.me/submissions/9d7be834-39c5-4693-a5b0-2de6902c4611

-- Generated from ChapterFriedrichsCanonical.lean — solution of BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_canonical
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Theorems.Thm_BookProof_FriedrichsCanonical_friedrichsOp_isPositiveSelfAdjointExtension
import Theorems.Thm_BookProof_QgHermiteFriedrichs_continuous_scalaronW
import Theorems.Thm_BookProof_QgHermiteFriedrichs_expBounded_scalaronW
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Theorems.Thm_BookProof_FriedrichsCanonical_qgScalaronPosSymOp_dense
open BookProof.FriedrichsCanonical




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom
open BookProof.HermiteProductCore
open BookProof.QgHermiteFriedrichs
open BookProof.YangMillsFriedrichs

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) :
    IsPositiveSelfAdjointExtension
      (hamCore (scalaronW M alpha) (continuous_scalaronW M alpha) (expBounded_scalaronW M alpha hM))
      (friedrichsOp (qgScalaronPosSymOp M alpha hM halpha)
        (qgScalaronPosSymOp_dense M alpha hM halpha)) :=
  friedrichsOp_isPositiveSelfAdjointExtension (qgScalaronPosSymOp M alpha hM halpha)
      (qgScalaronPosSymOp_dense M alpha hM halpha)
