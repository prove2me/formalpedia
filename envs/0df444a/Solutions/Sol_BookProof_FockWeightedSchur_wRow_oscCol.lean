-- Prove2me | solution 1 for BookProof.FockWeightedSchur.wRow_oscCol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T10:01:04.977613+00:00
-- url     : https://prove2.me/submissions/fa2068d6-2b40-4fd4-9dc4-dc491b2709fe

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.wRow_oscCol
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_oscW_pos
import Theorems.Thm_BookProof_FockWeightedSchur_support_oscCol_subset
import Theorems.Thm_BookProof_FockWeightedSchur_sum_pair_le
import Theorems.Thm_BookProof_FockWeightedSchur_norm_oscCol_le
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.FockWeightedSchur




open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {w : ℕ → ℝ}
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution : WRowBound oscW oscCol 2 := by

  intro k
  exact sum_pair_le (support_oscCol_subset k) (fun j => norm_nonneg _)
    (fun j => norm_oscCol_le k j) (le_of_lt (oscW_pos k))
