-- Prove2me | solution 1 for BookProof.YangMillsHermite.piOps_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:44:57.175162+00:00
-- url     : https://prove2.me/submissions/27b28aa3-3c66-4ce1-98b2-d94a296978ef

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.piOps_symmetricOn
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
import Theorems.Thm_BookProof_YangMillsHermite_momOp_polySym
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_symmetricOn_op
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

















































variable {D : Submodule ℂ (L2d d)}












variable {D : Submodule ℂ (L2d 99)}

set_option maxHeartbeats 1000000 in
theorem solution (Φ : CoreRep 99 D) (m : Fin 24) :
    SymmetricOn D (D.subtype.comp (piOps Φ m)) := Φ.symmetricOn_op (momOp_polySym _)
