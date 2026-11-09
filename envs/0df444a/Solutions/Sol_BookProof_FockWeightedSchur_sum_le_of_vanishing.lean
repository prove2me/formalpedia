-- Prove2me | solution 1 for BookProof.FockWeightedSchur.sum_le_of_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T09:52:57.322963+00:00
-- url     : https://prove2.me/submissions/ff907522-a512-4c61-a4af-7d33a74f7bda

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.sum_le_of_vanishing
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
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

theorem solution {f : ℕ → ℝ} {S L : Finset ℕ} (hf : ∀ j, 0 ≤ f j)
    (hz : ∀ j, j ∉ S → f j = 0) : ∑ j ∈ L, f j ≤ ∑ j ∈ S, f j := by
  classical
  have h1 : ∑ j ∈ L, f j = ∑ j ∈ L ∩ S, f j := by
    refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
    intro j hj hjn
    exact hz j fun hs => hjn (Finset.mem_inter.mpr ⟨hj, hs⟩)
  rw [h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun j _ _ => hf j
