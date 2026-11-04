-- Prove2me | solution 1 for BookProof.SmOuterFock.sm_dGamma_stone_flow
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T23:01:59.677277+00:00
-- url     : https://prove2.me/submissions/93ffae1e-e5ae-481b-b11e-dbe513a80dad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSmOuterFock.lean — solution of BookProof.SmOuterFock.sm_dGamma_stone_flow
import Mathlib
import Definitions.Def_ChapterSmOuterFock
import Theorems.Thm_BookProof_SmOuterFock_smFockCore_dense
import Theorems.Thm_BookProof_SmOuterFock_sm_dGamma_friedrichs_extension
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_positive
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterSmHamiltonian
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.SmOuterFock




open MvPolynomial
open BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.StoneBridge
open BookProof.ChapterStoneResolvent
open BookProof.HermiteProductCore
open BookProof.SmHamiltonian
open BookProof.StoneBridge
open BookProof.YangMillsFriedrichs

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (P : SmParams) :
    ∃ (T : UnboundedSelfAdjoint smFockSpace) (U : ℝ → (smFockSpace →L[ℂ] smFockSpace)),
      IsStoneFlow T U := by

  obtain ⟨Dom, A, hA⟩ := sm_dGamma_friedrichs_extension P
  obtain ⟨T, U, _, _, hflow⟩ := exists_stone_flow_of_positive smFockCore_dense hA
  exact ⟨T, U, hflow⟩
