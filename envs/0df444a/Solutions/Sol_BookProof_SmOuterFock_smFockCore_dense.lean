-- Prove2me | solution 1 for BookProof.SmOuterFock.smFockCore_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T22:50:52.75017+00:00
-- url     : https://prove2.me/submissions/8c44c7c9-1945-43fc-a731-60853a6814c4

-- Generated from ChapterSmOuterFock.lean — solution of BookProof.SmOuterFock.smFockCore_dense
import Mathlib
import Definitions.Def_ChapterSmOuterFock
import Theorems.Thm_BookProof_DirectSumEsa_dsCore_dense
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterSmHamiltonian
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
open BookProof.SmOuterFock




open MvPolynomial
open BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.StoneBridge
open BookProof.ChapterStoneResolvent
open BookProof.HermiteProductCore

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution :
    Dense ((smFockCore : Submodule ℂ smFockSpace) : Set smFockSpace) := dsCore_dense fun _ => polyGaussCore_dense
