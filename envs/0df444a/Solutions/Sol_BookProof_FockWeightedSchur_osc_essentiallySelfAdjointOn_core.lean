-- Prove2me | solution 1 for BookProof.FockWeightedSchur.osc_essentiallySelfAdjointOn_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T11:24:41.667352+00:00
-- url     : https://prove2.me/submissions/c66c701f-b249-4145-8c5c-edd937900354
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.osc_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_dGamma_essentiallySelfAdjointOn_core_w
import Theorems.Thm_BookProof_FockWeightedSchur_oscW_ge_one
import Theorems.Thm_BookProof_FockWeightedSchur_isHermCol_oscCol
import Theorems.Thm_BookProof_FockWeightedSchur_wRow_oscCol
import Theorems.Thm_BookProof_FockWeightedSchur_wCol_oscCol
import Theorems.Thm_BookProof_FockWeightedSchur_wComm_oscCol
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.FockWeightedSchur




open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.FockSecondQuantization

noncomputable section

variable {w : ℕ → ℝ}
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp oscCol) :=
  dGamma_essentiallySelfAdjointOn_core_w (w := oscW) (K := 2) (B := 4) oscW_ge_one
      isHermCol_oscCol wRow_oscCol wCol_oscCol (by norm_num) wComm_oscCol
