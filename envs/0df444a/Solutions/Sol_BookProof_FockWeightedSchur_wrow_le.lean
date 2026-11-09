-- Prove2me | solution 1 for BookProof.FockWeightedSchur.wrow_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T09:54:11.524885+00:00
-- url     : https://prove2.me/submissions/247d6950-3f01-43d0-bf11-e0efe2d95e78

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.wrow_le
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_sum_le_of_vanishing
import Theorems.Thm_BookProof_FockWeightedSchur_w_pos
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
theorem solution (hw : ∀ k, 1 ≤ w k) (hK : WRowBound w col K) (k : ℕ) (L : Finset ℕ) :
    ∑ j ∈ L, ‖(col k) j‖ / w k ≤ K := by

  classical
  have hwk : 0 < w k := w_pos hw k
  refine le_trans (sum_le_of_vanishing (S := (col k).support)
    (fun j => div_nonneg (norm_nonneg _) hwk.le) ?_) ?_
  · intro j hj
    rw [Finsupp.notMem_support_iff.mp hj]
    simp
  · rw [← Finset.sum_div, div_le_iff₀ hwk]
    exact le_trans (hK k) (le_of_eq (by ring))
