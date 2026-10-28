-- Prove2me | solution 1 for BookProof.QgOuterFockInteractionFL.QgFamily.secData_commForm_le
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T05:28:36.702819+00:00
-- url     : https://prove2.me/submissions/d29e27e4-395c-4872-887b-d36dc3f20f84

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Theorems.Thm_BookProof_SqSumFarisLavine_commForm_sqSumOp_le
import Theorems.Thm_BookProof_SqSumFarisLavine_sum_gradFun_sq_le_of_schur
import Theorems.Thm_BookProof_QgOuterFockCoreFL_commForm_congr
import Theorems.Thm_BookProof_QgOuterFockCoreFL_quadForm_congr
import Theorems.Thm_BookProof_QgOuterFockFL_harmFried_op_core
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockCoreFL
open BookProof.HermiteProductCore
open BookProof.QgHermiteOscillator
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.QgOuterFockInteractionFL
open BookProof.QgOuterFockInteractionFL.QgFamily



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL
open BookProof.Qg3DGaugeEsa BookProof.QuantumGravity3DGauge
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine

noncomputable section

variable (F : QgFamily)

theorem solution (F : QgFamily) (n : ℕ) (p : (F.secData n).C₀) :
    |commForm (F.secData n).H₀ (F.secData n).coreN p|
      ≤ F.flc * quadForm (F.secData n).coreN p := by
  have hN : (F.secData n).coreN p = BookProof.QgHermiteOscillator.harmCore p := by
    change (harmFried (n * 84)).op (Submodule.inclusion _ p) = _
    exact (BookProof.QgOuterFockFL.harmFried_op_core (n * 84) p _).trans rfl
  have hc : commForm (F.secData n).H₀ (F.secData n).coreN p
      = commForm (sqSumOp (F.kap n) (F.vv n)) BookProof.QgHermiteOscillator.harmCore p :=
    BookProof.QgOuterFockCoreFL.commForm_congr _ _ _ _ p p rfl hN
  have hq : quadForm (F.secData n).coreN p = quadForm BookProof.QgHermiteOscillator.harmCore p :=
    BookProof.QgOuterFockCoreFL.quadForm_congr _ _ p p rfl hN
  rw [hc, hq]
  exact BookProof.SqSumFarisLavine.commForm_sqSumOp_le F.km_nonneg (F.kap_le n) F.ab_nonneg
    (BookProof.SqSumFarisLavine.sum_gradFun_sq_le_of_schur F.a_nonneg F.b_nonneg
      (F.row_le n) (F.col_le n)) p
