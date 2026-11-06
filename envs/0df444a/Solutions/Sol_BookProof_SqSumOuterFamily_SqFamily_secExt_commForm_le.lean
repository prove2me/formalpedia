-- Prove2me | solution 1 for BookProof.SqSumOuterFamily.SqFamily.secExt_commForm_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T23:27:01.54701+00:00
-- url     : https://prove2.me/submissions/80673998-00ec-49fd-a10f-eae6f829db05

-- Generated from ChapterSqSumOuterFamily.lean — solution of BookProof.SqSumOuterFamily.SqFamily.secExt_commForm_le
import Mathlib
import Definitions.Def_ChapterSqSumOuterFamily
import Theorems.Thm_BookProof_SqSumOuterFamily_SqFamily_secData_commForm_le
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_commForm_le
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockFarisLavine
open BookProof.SqSumOuterFamily
open BookProof.SqSumOuterFamily.SqFamily




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine
open BookProof.HermiteProductCore
open BookProof.QgOuterFockFL

noncomputable section

variable (dim : ℕ → ℕ)
variable (F : SqFamily)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (u : (harmFried (F.dim n)).dom) :
    |commForm (F.secExt n) (harmFried (F.dim n)).op u|
      ≤ F.flc * quadForm (harmFried (F.dim n)).op u := (F.secData n).ext_commForm_le (F.secData_commForm_le n) u
