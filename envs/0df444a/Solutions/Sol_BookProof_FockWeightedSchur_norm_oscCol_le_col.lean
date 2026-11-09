-- Prove2me | solution 1 for BookProof.FockWeightedSchur.norm_oscCol_le_col
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T10:01:00.969851+00:00
-- url     : https://prove2.me/submissions/89fd1806-371f-4aaa-b5df-b368beadb750

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.norm_oscCol_le_col
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_sqrt_le_of_one_le
import Theorems.Thm_BookProof_FockWeightedSchur_norm_oscCol_apply
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
theorem solution (j k : ℕ) : ‖(oscCol j) k‖ ≤ oscW k := by

  rw [norm_oscCol_apply]
  have hj0 : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  by_cases h1 : k = j + 1
  · rw [if_pos h1]
    have hkj : (k : ℝ) = (j : ℝ) + 1 := by rw [h1]; push_cast; ring
    have := sqrt_le_of_one_le (a := (j : ℝ) + 1) (by linarith)
    simp only [oscW]; linarith
  · by_cases h2 : j = k + 1
    · rw [if_neg h1, if_pos h2]
      have hjk : (j : ℝ) = (k : ℝ) + 1 := by rw [h2]; push_cast; ring
      have := sqrt_le_of_one_le (a := (j : ℝ)) (by rw [hjk]; linarith)
      simp only [oscW]; linarith
    · rw [if_neg h1, if_neg h2]
      simp only [oscW]; linarith
