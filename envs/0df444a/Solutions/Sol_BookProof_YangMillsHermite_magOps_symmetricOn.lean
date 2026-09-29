-- Prove2me | solution 1 for BookProof.YangMillsHermite.magOps_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:43:17.272971+00:00
-- url     : https://prove2.me/submissions/fcfcc684-eb10-4612-acc8-14a80afd1629

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.magOps_symmetricOn
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
import Theorems.Thm_BookProof_YangMillsHermite_mulOp_polySym
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_symmetricOn_op
import Theorems.Thm_BookProof_YangMillsHermite_realCoeff_magPoly
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

















































variable {D : Submodule ℂ (L2d d)}












variable {D : Submodule ℂ (L2d 99)}

set_option maxHeartbeats 1000000 in
theorem solution (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (m : Fin 24) :
    SymmetricOn D (D.subtype.comp (magOps Φ fabc m)) := Φ.symmetricOn_op (mulOp_polySym (realCoeff_magPoly fabc _ _))
