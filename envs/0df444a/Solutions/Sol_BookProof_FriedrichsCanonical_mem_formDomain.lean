-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.mem_formDomain
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:39:43.439093+00:00
-- url     : https://prove2.me/submissions/0fba2c05-78ea-4245-9505-01b6cd01e86f

-- Generated from ChapterFriedrichsCanonical.lean — solution of BookProof.FriedrichsCanonical.mem_formDomain
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
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
theorem solution {P : PosSymOp F} {v : F} (k : FormSpace P) (hk : formExt P k = v) :
    v ∈ formDomain P := ⟨k, hk⟩
