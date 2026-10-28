-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.qgWeylProd_coord_mom_polySym
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T04:40:29.354116+00:00
-- url     : https://prove2.me/submissions/ca8fcb05-78d8-477e-96da-f8c41872a471

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Theorems.Thm_BookProof_YangMillsHermite_weylProd_polySym
import Theorems.Thm_BookProof_YangMillsHermite_mulOp_polySym
import Theorems.Thm_BookProof_YangMillsHermite_momOp_polySym
import Theorems.Thm_BookProof_YangMillsHermite_realCoeff_X
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {d : ℕ}

theorem solution (j k : Fin d) :
    PolySym (qgWeylProd (mulOp (X j)) (momOp k)) :=
  BookProof.YangMillsHermite.weylProd_polySym
    (BookProof.YangMillsHermite.mulOp_polySym (BookProof.YangMillsHermite.realCoeff_X j))
    (BookProof.YangMillsHermite.momOp_polySym k)
