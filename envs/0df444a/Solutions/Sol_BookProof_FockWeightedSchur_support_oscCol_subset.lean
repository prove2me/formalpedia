-- Prove2me | solution 1 for BookProof.FockWeightedSchur.support_oscCol_subset
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T10:00:35.25032+00:00
-- url     : https://prove2.me/submissions/544a6ff5-1bec-43c9-ae3b-9e581405a8aa

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.support_oscCol_subset
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_oscCol_apply
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
theorem solution (k : ℕ) : (oscCol k).support ⊆ {k + 1, k - 1} := by

  classical
  intro j hj
  have hne : (oscCol k) j ≠ 0 := Finsupp.mem_support_iff.mp hj
  rw [oscCol_apply] at hne
  by_cases h1 : j = k + 1
  · simp [h1]
  · by_cases h2 : k = j + 1
    · have : j = k - 1 := by omega
      simp [this]
    · rw [if_neg h1, if_neg h2] at hne
      exact absurd rfl hne
