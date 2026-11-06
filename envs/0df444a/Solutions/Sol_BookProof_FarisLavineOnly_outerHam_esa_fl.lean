-- Prove2me | solution 1 for BookProof.FarisLavineOnly.outerHam_esa_fl
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T23:05:20.146825+00:00
-- url     : https://prove2.me/submissions/992568cc-4bb0-4bc0-8d77-4346b6772f2a

-- Generated from ChapterFarisLavineOnly.lean — solution of BookProof.FarisLavineOnly.outerHam_esa_fl
import Mathlib
import Definitions.Def_ChapterFarisLavineOnly
import Theorems.Thm_BookProof_FarisLavineOnly_secHam_esa_fl
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_essentiallySelfAdjointOn
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterSqSumOuterFamily
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL
open BookProof.FarisLavineOnly



open scoped ENNReal

noncomputable section


open BookProof.FarisLavine


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]


variable (d : CoreData F)







open Finset
open BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.HermiteProductCore BookProof.QgHermiteOscillator
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL BookProof.SqSumOuterFamily
open BookProof.HermiteProductCore

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (d : CoreData F)

set_option maxHeartbeats 1000000 in
theorem solution (F : SqFamily) :
    EssentiallySelfAdjointOn (outerCore F.dim) F.outerHam := dsOp_essentiallySelfAdjointOn _ fun n => secHam_esa_fl F n
