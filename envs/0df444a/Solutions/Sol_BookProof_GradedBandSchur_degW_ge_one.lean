-- Prove2me | solution 1 for BookProof.GradedBandSchur.degW_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T16:48:16.096044+00:00
-- url     : https://prove2.me/submissions/88bdafed-a90a-4ef0-a04a-15086ff2f3a2

-- Generated from ChapterGradedBandSchurEsa.lean — solution of BookProof.GradedBandSchur.degW_ge_one
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

theorem solution (deg : ℕ → ℕ) (k : ℕ) : 1 ≤ degW deg k := by
  simp only [degW]
  have : (0:ℝ) ≤ (deg k : ℝ) := Nat.cast_nonneg _
  linarith
