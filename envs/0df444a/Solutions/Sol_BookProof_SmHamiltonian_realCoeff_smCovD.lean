-- Prove2me | solution 1 for BookProof.SmHamiltonian.realCoeff_smCovD
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:19:14.374953+00:00
-- url     : https://prove2.me/submissions/d64f4cae-10d7-48c5-b8de-ef8d1cf48cfe

-- Generated from ChapterSmHamiltonian.lean — solution of BookProof.SmHamiltonian.realCoeff_smCovD
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_add
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_mul
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_smul
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_sum
import Theorems.Thm_BookProof_YangMillsHermite_realCoeff_X
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterSirkFinitePrecision
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsHermite
open BookProof.SmHamiltonian




open MvPolynomial
open BookProof.SmOneParticle
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension

noncomputable section

variable {D : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (P : SmParams) (co : Fin 163 → Fin D) (a : Fin 4) (i : Fin 3) :
    RealCoeff (smCovD P co a i) := by

  refine RealCoeff.add (RealCoeff.add (realCoeff_X _) (RealCoeff.smul ?_)) (RealCoeff.smul ?_)
  · exact RealCoeff.sum fun j _ => RealCoeff.sum fun b _ =>
      RealCoeff.smul ((realCoeff_X _).mul (realCoeff_X _))
  · exact RealCoeff.sum fun b _ => RealCoeff.smul ((realCoeff_X _).mul (realCoeff_X _))
