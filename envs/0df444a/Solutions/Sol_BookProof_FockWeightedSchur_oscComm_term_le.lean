-- Prove2me | solution 1 for BookProof.FockWeightedSchur.oscComm_term_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T10:01:42.593208+00:00
-- url     : https://prove2.me/submissions/1bc99a6f-6d35-4dba-8e10-e616563fbe03

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.oscComm_term_le
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_sqrt_le_of_one_le
import Theorems.Thm_BookProof_FockWeightedSchur_oscW_pos
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
theorem solution (k j : ℕ) :
    ‖(oscCol k) j‖ * |oscW j ^ 2 - oscW k ^ 2| / (oscW k * oscW j) ≤ 2 := by

  have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hj0 : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hwk : 0 < oscW k := oscW_pos k
  have hwj : 0 < oscW j := oscW_pos j
  rw [div_le_iff₀ (mul_pos hwk hwj), norm_oscCol_apply]
  by_cases h1 : j = k + 1
  · rw [if_pos h1]
    have hj : oscW j = (k : ℝ) + 2 := by
      simp only [oscW, h1]; push_cast; ring
    have hkk : oscW k = (k : ℝ) + 1 := rfl
    have habs : |oscW j ^ 2 - oscW k ^ 2| = 2 * (k : ℝ) + 3 := by
      rw [hj, hkk, abs_of_nonneg (by nlinarith)]
      ring
    rw [habs, hj, hkk]
    have hs : Real.sqrt ((k : ℝ) + 1) ≤ (k : ℝ) + 1 :=
      sqrt_le_of_one_le (by linarith)
    have hs0 : 0 ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_nonneg _
    nlinarith [hs, hs0]
  · by_cases h2 : k = j + 1
    · rw [if_neg h1, if_pos h2]
      have hk1 : (1:ℝ) ≤ (k : ℝ) := by
        have : (1:ℕ) ≤ k := by omega
        exact_mod_cast this
      have hjk : (j : ℝ) = (k : ℝ) - 1 := by
        have : (k : ℝ) = (j : ℝ) + 1 := by rw [h2]; push_cast; ring
        linarith
      have hj : oscW j = (k : ℝ) := by simp only [oscW, hjk]; ring
      have hkk : oscW k = (k : ℝ) + 1 := rfl
      have habs : |oscW j ^ 2 - oscW k ^ 2| = 2 * (k : ℝ) + 1 := by
        rw [hj, hkk, abs_of_nonpos (by nlinarith)]
        ring
      rw [habs, hj, hkk]
      have hs : Real.sqrt (k : ℝ) ≤ (k : ℝ) := sqrt_le_of_one_le hk1
      have hs0 : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
      nlinarith [hs, hs0]
    · rw [if_neg h1, if_neg h2]
      have : 0 < oscW k * oscW j := mul_pos hwk hwj
      nlinarith
