-- Prove2me | solution 1 for BookProof.SmHamiltonian.smPi_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:19:16.253727+00:00
-- url     : https://prove2.me/submissions/70539661-4342-48f7-bed9-ec7c8490961f

-- Generated from ChapterSmHamiltonian.lean — solution of BookProof.SmHamiltonian.smPi_symmetricOn
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_symmetricOn_op
import Theorems.Thm_BookProof_YangMillsHermite_momOp_polySym
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
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
theorem solution (m : Fin 40) :
    SymmetricOn (polyGaussCore (d := 163))
      ((polyGaussCore (d := 163)).subtype.comp (smPi m)) := (coreRepPoly 163).symmetricOn_op (momOp_polySym _)
