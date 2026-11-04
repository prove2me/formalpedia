-- Prove2me | solution 1 for BookProof.SmOuterFock.smSecPi_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T22:50:32.585664+00:00
-- url     : https://prove2.me/submissions/49d22cbb-2a5f-4fb1-8afb-42545ef7c7fd

-- Generated from ChapterSmOuterFock.lean — solution of BookProof.SmOuterFock.smSecPi_symmetricOn
import Mathlib
import Definitions.Def_ChapterSmOuterFock
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_symmetricOn_op
import Theorems.Thm_BookProof_YangMillsHermite_momOp_polySym
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterSmHamiltonian
import Definitions.Def_ChapterYangMillsHermite
open BookProof.SmOuterFock




open MvPolynomial
open BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.StoneBridge
open BookProof.ChapterStoneResolvent
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.SmHamiltonian
open BookProof.YangMillsHermite

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (m : Fin (n * 40)) :
    SymmetricOn (polyGaussCore (d := n * 163))
      ((polyGaussCore (d := n * 163)).subtype.comp (smSecPi n m)) := (coreRepPoly (n * 163)).symmetricOn_op (momOp_polySym _)
