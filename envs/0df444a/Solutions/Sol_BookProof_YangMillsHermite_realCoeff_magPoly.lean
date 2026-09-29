-- Prove2me | solution 1 for BookProof.YangMillsHermite.realCoeff_magPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T04:19:32.613497+00:00
-- url     : https://prove2.me/submissions/f30c312a-8e8a-4b2d-93ee-23358cfbadc7

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.realCoeff_magPoly
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_add
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_mul
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_smul
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_sum
import Theorems.Thm_BookProof_YangMillsHermite_realCoeff_X
import Theorems.Thm_BookProof_YangMillsHermite_PolySym_add
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

















































variable {D : Submodule ℂ (L2d d)}












variable {D : Submodule ℂ (L2d 99)}

set_option maxHeartbeats 1000000 in
theorem solution (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (i : Fin 3) (a : Fin 8) :
    RealCoeff (magPoly fabc i a) := by

  refine RealCoeff.sum fun j _ => RealCoeff.sum fun k _ => RealCoeff.smul ?_
  refine RealCoeff.add (realCoeff_X _) ?_
  exact RealCoeff.sum fun b _ => RealCoeff.sum fun c _ =>
    RealCoeff.smul ((realCoeff_X _).mul (realCoeff_X _))
