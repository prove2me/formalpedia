-- Prove2me | solution 1 for BookProof.SmHamiltonian.realCoeff_smMagG
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:02:45.102819+00:00
-- url     : https://prove2.me/submissions/7c0692d4-230f-421c-9754-899ca361659e

-- Generated from ChapterSmHamiltonian.lean — solution of BookProof.SmHamiltonian.realCoeff_smMagG
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
import Theorems.Thm_BookProof_SmHamiltonian_RealCoeff_sub_prime
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
theorem solution (P : SmParams) (co : Fin 163 → Fin D) (a : Fin 8) (i : Fin 3) :
    RealCoeff (smMagG P co a i) := by

  refine RealCoeff.smul (RealCoeff.sum fun j _ => RealCoeff.sum fun k _ => RealCoeff.smul ?_)
  refine RealCoeff.add (RealCoeff.sub_prime (realCoeff_X _) (realCoeff_X _)) ?_
  exact RealCoeff.smul (RealCoeff.sum fun b _ => RealCoeff.sum fun d _ =>
    RealCoeff.smul ((realCoeff_X _).mul (realCoeff_X _)))
