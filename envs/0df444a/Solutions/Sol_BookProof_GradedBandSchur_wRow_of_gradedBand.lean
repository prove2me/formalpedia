-- Prove2me | solution 1 for BookProof.GradedBandSchur.wRow_of_gradedBand
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T16:48:23.980707+00:00
-- url     : https://prove2.me/submissions/87ddb032-c3fc-4348-98d4-ec74a69e0110

-- Generated from ChapterGradedBandSchurEsa.lean — solution of BookProof.GradedBandSchur.wRow_of_gradedBand
import Mathlib
import Definitions.Def_ChapterGradedBandSchurEsaPromoted
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFockWeightedSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.GradedBandSchur




open BookProof.FockSecondQuantization BookProof.FockSchur BookProof.FockWeightedSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow

noncomputable section

variable {col : ℕ → (ℕ →₀ ℂ)} {deg : ℕ → ℕ} {D M : ℕ} {C : ℝ}

variable {col : ℕ → (ℕ →₀ ℂ)} {deg : ℕ → ℕ} {D M : ℕ} {C : ℝ}

set_option maxHeartbeats 1000000 in

theorem solution (hC : 0 ≤ C)
    (hcard : ∀ k, (col k).support.card ≤ M)
    (hent : ∀ k j, ‖(col k) j‖ ≤ C * ((deg k : ℝ) + 1)) :
    WRowBound (degW deg) col (C * M) := by
  intro k
  calc ∑ j ∈ (col k).support, ‖(col k) j‖
      ≤ (col k).support.card • (C * ((deg k : ℝ) + 1)) :=
        Finset.sum_le_card_nsmul _ _ _ fun j _ => hent k j
    _ = (col k).support.card * (C * ((deg k : ℝ) + 1)) := by rw [nsmul_eq_mul]
    _ ≤ M * (C * ((deg k : ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_right (by exact_mod_cast hcard k) ?_
        have : (0:ℝ) ≤ (deg k : ℝ) + 1 := by positivity
        exact mul_nonneg hC this
    _ = C * M * degW deg k := by simp only [degW]; ring
