-- Prove2me | solution 1 for BookProof.SmHamiltonian.realCoeff_smMagB
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:02:47.775693+00:00
-- url     : https://prove2.me/submissions/e12e4afd-02fe-44f6-ac90-088a78126ef2

-- Generated from ChapterSmHamiltonian.lean — solution of BookProof.SmHamiltonian.realCoeff_smMagB
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
import Theorems.Thm_BookProof_SmHamiltonian_RealCoeff_sub_prime
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_smul
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_sum
import Theorems.Thm_BookProof_YangMillsHermite_realCoeff_X
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
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
theorem solution (co : Fin 163 → Fin D) (i : Fin 3) : RealCoeff (smMagB co i) :=
  RealCoeff.smul (RealCoeff.sum fun _ _ => RealCoeff.sum fun _ _ =>
      RealCoeff.smul (RealCoeff.sub_prime (realCoeff_X _) (realCoeff_X _)))
