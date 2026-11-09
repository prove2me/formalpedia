-- Prove2me | solution 1 for BookProof.FockWeightedSchur.wComm_oscCol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T10:19:38.585182+00:00
-- url     : https://prove2.me/submissions/de8f7307-1a6b-4bbd-89bb-bb2f581707f3

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.wComm_oscCol
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_oscW_pos
import Theorems.Thm_BookProof_FockWeightedSchur_support_oscCol_subset
import Theorems.Thm_BookProof_FockWeightedSchur_sum_pair_le
import Theorems.Thm_BookProof_FockWeightedSchur_oscComm_term_le
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
theorem solution : WCommBound oscW oscCol 4 := by

  intro k
  have h := sum_pair_le
    (f := fun j => ‖(oscCol k) j‖ * |oscW j ^ 2 - oscW k ^ 2| / (oscW k * oscW j)) (C := 2)
    (support_oscCol_subset k)
    (fun j => by
      have : 0 < oscW k * oscW j := mul_pos (oscW_pos k) (oscW_pos j)
      positivity)
    (fun j => oscComm_term_le k j) (by norm_num)
  exact le_trans h (by norm_num)
