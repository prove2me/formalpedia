-- Prove2me | solution 1 for BookProof.FockWeightedSchur.isHermCol_oscCol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T11:20:15.666409+00:00
-- url     : https://prove2.me/submissions/93c49e18-c617-474a-adc3-a5de792c382f

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.isHermCol_oscCol
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_oscCol_apply
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockWeightedSchur




open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.FockSecondQuantization

noncomputable section

variable {w : ℕ → ℝ}
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution : IsHermCol oscCol := by

  intro j k
  rw [oscCol_apply, oscCol_apply]
  by_cases h1 : k = j + 1
  · have h2 : ¬(j = k + 1) := by omega
    rw [if_pos h1, if_neg h2, if_pos h1, Complex.conj_ofReal]
    have : ((k : ℝ)) = (j : ℝ) + 1 := by rw [h1]; push_cast; ring
    rw [this]
  · by_cases h2 : j = k + 1
    · rw [if_neg h1, if_pos h2, if_pos h2, Complex.conj_ofReal]
      have : ((j : ℝ)) = (k : ℝ) + 1 := by rw [h2]; push_cast; ring
      rw [this]
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
      simp
