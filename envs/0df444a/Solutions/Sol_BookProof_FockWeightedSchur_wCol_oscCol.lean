-- Prove2me | solution 1 for BookProof.FockWeightedSchur.wCol_oscCol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T10:01:24.196337+00:00
-- url     : https://prove2.me/submissions/7b64938b-7b53-4682-ad21-5f3768ecc7fd

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.wCol_oscCol
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_oscW_pos
import Theorems.Thm_BookProof_FockWeightedSchur_support_oscCol_subset
import Theorems.Thm_BookProof_FockWeightedSchur_sum_pair_le
import Theorems.Thm_BookProof_FockWeightedSchur_norm_oscCol_le_col
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
theorem solution : WColBound oscW oscCol 2 := by

  intro j
  have h := sum_pair_le (f := fun k => ‖(oscCol j) k‖ / oscW k) (C := 1)
    (support_oscCol_subset j) (fun k => div_nonneg (norm_nonneg _) (oscW_pos k).le)
    (fun k => by
      rw [div_le_one (oscW_pos k)]
      exact norm_oscCol_le_col j k) zero_le_one
  simpa using h
