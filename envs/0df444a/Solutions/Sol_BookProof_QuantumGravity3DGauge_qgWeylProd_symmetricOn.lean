-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.qgWeylProd_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:34:41.935998+00:00
-- url     : https://prove2.me/submissions/93be52ae-f019-4857-bffb-d0855221876c

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Theorems.Thm_BookProof_YangMillsHermite_weylProd_polySym
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_symmetricOn_op
import Theorems.Thm_BookProof_YangMillsHermite_mulOp_polySym
import Theorems.Thm_BookProof_YangMillsHermite_momOp_polySym
-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.qgWeylProd_symmetricOn
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {D : Submodule ℂ (L2d 84)}


theorem solution (Φ : CoreRep 84 D) (j k : Fin 84) :
    SymmetricOn D (D.subtype.comp (Φ.op (qgWeylProd (mulOp (X j)) (momOp k)))) := by
  have hX : BookProof.YangMillsHermite.RealCoeff (X j : MvPolynomial (Fin 84) ℂ) := by
    simp [BookProof.YangMillsHermite.RealCoeff, BookProof.YangMillsHermite.starP]
  exact BookProof.YangMillsHermite.CoreRep.symmetricOn_op Φ
    (BookProof.YangMillsHermite.weylProd_polySym (BookProof.YangMillsHermite.mulOp_polySym hX)
      (BookProof.YangMillsHermite.momOp_polySym k))

