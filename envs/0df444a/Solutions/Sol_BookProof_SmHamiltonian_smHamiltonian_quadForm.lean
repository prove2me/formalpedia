-- Prove2me | solution 1 for BookProof.SmHamiltonian.smHamiltonian_quadForm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:12:12.465978+00:00
-- url     : https://prove2.me/submissions/c76a93c8-07d0-4418-9d46-9153e1753819

-- Generated from ChapterSmHamiltonian.lean — solution of BookProof.SmHamiltonian.smHamiltonian_quadForm
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
theorem solution (P : SmParams) (x : polyGaussCore (d := 163)) :
    quadForm (smHamiltonian P) x
      = 1 / 2 * (∑ m, ‖((smPi m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2)
        + 1 / 2 * ∑ r, ‖((smField P r x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := weylOpDom_quadForm smPi_symmetricOn (smField_symmetricOn P) x
