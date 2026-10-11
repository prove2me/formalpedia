-- Prove2me | solution 1 for BookProof.SmHamiltonian.realCoeff_smMagW
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:02:46.530899+00:00
-- url     : https://prove2.me/submissions/ac262368-c0d6-4ffd-a904-52e7a9eb39b1

-- Generated from ChapterSmHamiltonian.lean — solution of BookProof.SmHamiltonian.realCoeff_smMagW
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
theorem solution (P : SmParams) (co : Fin 163 → Fin D) (m i : Fin 3) :
    RealCoeff (smMagW P co m i) := by

  refine RealCoeff.smul (RealCoeff.sum fun j _ => RealCoeff.sum fun k _ => RealCoeff.smul ?_)
  refine RealCoeff.add (RealCoeff.sub_prime (realCoeff_X _) (realCoeff_X _)) ?_
  exact RealCoeff.smul (RealCoeff.sum fun b _ => RealCoeff.sum fun d _ =>
    RealCoeff.smul ((realCoeff_X _).mul (realCoeff_X _)))
