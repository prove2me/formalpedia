-- Prove2me | solution 1 for BookProof.YangMillsGhost.ymGhostHam_add_bounded_coupling_esa
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:25:06.661805+00:00
-- url     : https://prove2.me/submissions/ec9ee6f2-8f85-448c-b690-438050c6cecd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterYangMillsGhostSector.lean — solution of BookProof.YangMillsGhost.ymGhostHam_add_bounded_coupling_esa
import Mathlib
import Definitions.Def_ChapterYangMillsGhostSector
import Theorems.Thm_BookProof_YangMillsGhost_ymGhostHam_symmetricOn
import Theorems.Thm_BookProof_YangMillsGhost_ymGhostHam_essentiallySelfAdjointOn_core
import Theorems.Thm_BookProof_KatoRellich_essentiallySelfAdjointOn_add_bounded
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterYangMillsAbelianEsa
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
open BookProof.YangMillsGhost




noncomputable section

open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.YangMillsHermite BookProof.YangMillsAbelianEsa
open BookProof.KatoRellich BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.HermiteProductCore

variable {K : ℕ}

variable {K : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (ω : Fin K → ℝ)
    (B : GhostSpace K →L[ℂ] GhostSpace K)
    (hB : ∀ x y : GhostSpace K, (inner ℂ (B x) y : ℂ) = inner ℂ x (B y)) :
    EssentiallySelfAdjointOn (ghostCore K)
      (ymGhostHam 0 ω + (B.toLinearMap ∘ₗ (ghostCore K).subtype)) :=
  essentiallySelfAdjointOn_add_bounded _ (ymGhostHam_symmetricOn 0 ω)
      (ymGhostHam_essentiallySelfAdjointOn_core ω) B hB
