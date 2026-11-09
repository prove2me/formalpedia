-- Prove2me | solution 1 for BookProof.FockWeightedSchur.norm_oscCol_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T10:00:56.986025+00:00
-- url     : https://prove2.me/submissions/c34a0a1d-3445-4f54-981c-0787f9b55ebc

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.norm_oscCol_le
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
theorem solution (k j : ℕ) : ‖(oscCol k) j‖ ≤ oscW k := by

  rw [norm_oscCol_apply]
  have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  by_cases h1 : j = k + 1
  · rw [if_pos h1]
    have := sqrt_le_of_one_le (a := (k : ℝ) + 1) (by linarith)
    simpa [oscW] using this
  · by_cases h2 : k = j + 1
    · rw [if_neg h1, if_pos h2]
      have hk1 : (1:ℝ) ≤ (k : ℝ) := by
        have : (1:ℕ) ≤ k := by omega
        exact_mod_cast this
      have := sqrt_le_of_one_le hk1
      simp only [oscW]; linarith
    · rw [if_neg h1, if_neg h2]
      simp only [oscW]; linarith
