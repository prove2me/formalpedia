-- Prove2me | solution 1 for BookProof.SqSumOuterFamily.SqFamily.secData_commForm_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:09:53.067475+00:00
-- url     : https://prove2.me/submissions/1b7a9e79-4a49-431f-9064-57e42e12afce

import Definitions.Def_ChapterSqSumOuterFamily

open BookProof.HermiteProductCore
open BookProof.QgHermiteOscillator
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData

open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine
open BookProof.SqSumOuterFamily

noncomputable section

variable (dim : ℕ → ℕ)
variable (F : SqFamily)

theorem solution (n : ℕ) (p : (F.secData n).C₀) :
    |commForm (F.secData n).H₀ (F.secData n).coreN p|
      ≤ F.flc * quadForm (F.secData n).coreN p := by
  have hN : (F.secData n).coreN = BookProof.QgHermiteOscillator.harmCore := by
    apply LinearMap.ext
    intro q
    exact harmFried_op_core (F.dim n) q ((F.secData n).gc.le q.2)
  rw [hN]
  exact F.secHam_commForm_le n p
