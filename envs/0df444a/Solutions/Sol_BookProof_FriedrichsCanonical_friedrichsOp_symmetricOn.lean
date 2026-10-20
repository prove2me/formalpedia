-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.friedrichsOp_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T10:33:24.730615+00:00
-- url     : https://prove2.me/submissions/cc035f07-f9b6-44d2-ac7e-6b9585587fce

-- Generated from ChapterFriedrichsCanonical.lean — solution of BookProof.FriedrichsCanonical.friedrichsOp_symmetricOn
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Theorems.Thm_BookProof_FriedrichsCanonical_friedrichsOp_isPositiveSelfAdjointExtension
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFriedrichsExtension
open BookProof.FriedrichsCanonical




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) :
    SymmetricOn (friedrichsDomain P) (friedrichsOp P hdense) := (friedrichsOp_isPositiveSelfAdjointExtension P hdense).2.1
