-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.friedrichsOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T10:33:15.012138+00:00
-- url     : https://prove2.me/submissions/565388d5-de32-410e-a2f3-e661398abb63

-- Generated from ChapterFriedrichsCanonical.lean — solution of BookProof.FriedrichsCanonical.friedrichsOp_apply
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHashimotoShiftInvert
open BookProof.FriedrichsCanonical




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (P : PosSymOp F) (hdense : Dense (P.dom : Set F))
    (y : friedrichsDomain P) :
    friedrichsOp P hdense y
      = preim (friedrichsResolvent P) y - ((1 : ℝ) : ℂ) • (y : F) := rfl
