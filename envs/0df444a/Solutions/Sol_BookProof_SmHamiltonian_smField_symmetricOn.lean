-- Prove2me | solution 1 for BookProof.SmHamiltonian.smField_symmetricOn
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:19:17.14598+00:00
-- url     : https://prove2.me/submissions/a51babfb-ce49-4d4f-8dd1-fa680cd77ebf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSmHamiltonian.lean — solution of BookProof.SmHamiltonian.smField_symmetricOn
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
import Theorems.Thm_BookProof_SmHamiltonian_realCoeff_smFormPoly
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_symmetricOn_op
import Theorems.Thm_BookProof_YangMillsHermite_mulOp_polySym
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
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
theorem solution (P : SmParams) (r : Fin 49) :
    SymmetricOn (polyGaussCore (d := 163))
      ((polyGaussCore (d := 163)).subtype.comp (smField P r)) := (coreRepPoly 163).symmetricOn_op (mulOp_polySym (realCoeff_smFormPoly P _ _))
