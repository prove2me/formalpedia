-- Prove2me | solution 1 for BookProof.YangMillsGhost.ymGhostHam_stone_flow
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:32.732636+00:00
-- url     : https://prove2.me/submissions/3cb6a097-ca7f-4fc2-aace-a1c4e8ec0ce4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterYangMillsGhostSector.lean — solution of BookProof.YangMillsGhost.ymGhostHam_stone_flow
import Mathlib
import Definitions.Def_ChapterYangMillsGhostSector
import Theorems.Thm_BookProof_YangMillsGhost_ghostCore_dense
import Theorems.Thm_BookProof_YangMillsGhost_ymGhostHam_symmetricOn
import Theorems.Thm_BookProof_YangMillsGhost_ymGhostHam_essentiallySelfAdjointOn_core
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
open BookProof.YangMillsGhost















noncomputable section

open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.YangMillsHermite
open BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent

variable {K : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (ω : Fin K → ℝ) :
    ∃ (T : UnboundedSelfAdjoint (GhostSpace K)) (U : ℝ → (GhostSpace K →L[ℂ] GhostSpace K)),
      IsSelfAdjointExtension (ymGhostHam 0 ω) T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ ghostCore_dense (ymGhostHam_symmetricOn 0 ω)
      (ymGhostHam_essentiallySelfAdjointOn_core ω)
