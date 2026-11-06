-- Prove2me | solution 1 for BookProof.SqSumOuterFamily.SqFamily.secExt_core
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:34:06.556907+00:00
-- url     : https://prove2.me/submissions/55aa9cce-57a1-466f-b98b-c34af3b1ac16

import Definitions.Def_ChapterSqSumOuterFamily
import Definitions.Def_ChapterLeafGaps

open BookProof.HermiteProductCore
open BookProof.QgOuterFockFL

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

theorem solution (n : ℕ) (p : polyGaussCore (d := F.dim n))
    (h : (p : L2d (F.dim n)) ∈ (harmFried (F.dim n)).dom) :
    F.secExt n ⟨(p : L2d (F.dim n)), h⟩ = F.secHam n p :=
  (F.secData n).ext_core p
