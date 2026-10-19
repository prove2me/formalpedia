-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.qgScalaronPosSymOp_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:39:48.513661+00:00
-- url     : https://prove2.me/submissions/e58eeffe-d99d-4687-9bf4-de150adf1a6d

-- Generated from ChapterFriedrichsCanonical.lean — solution of BookProof.FriedrichsCanonical.qgScalaronPosSymOp_dense
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteProductCore
open BookProof.FriedrichsCanonical




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom
open BookProof.HermiteProductCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) :
    Dense (((qgScalaronPosSymOp M alpha hM halpha).dom : Submodule ℂ (L2d 1)) : Set (L2d 1)) := polyGaussCore_dense
