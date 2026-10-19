-- Prove2me | solution 1 for BookProof.SmHamiltonian.smHamiltonian_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:11:56.504987+00:00
-- url     : https://prove2.me/submissions/83f60e88-57ef-4b8b-9752-3b484dc901b8

-- Generated from ChapterSmHamiltonian.lean — solution of BookProof.SmHamiltonian.smHamiltonian_symmetricOn
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
import Theorems.Thm_BookProof_SmHamiltonian_smPi_symmetricOn
import Theorems.Thm_BookProof_SmHamiltonian_smField_symmetricOn
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.SmHamiltonian




open MvPolynomial
open BookProof.SmOneParticle
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension
open BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs

noncomputable section

variable {D : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (P : SmParams) :
    SymmetricOn (polyGaussCore (d := 163)) (smHamiltonian P) := weylOpDom_symmetricOn smPi_symmetricOn (smField_symmetricOn P)
