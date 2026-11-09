-- Prove2me | solution 1 for BookProof.GradedBandSchur.degW_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T16:48:20.062098+00:00
-- url     : https://prove2.me/submissions/c0378601-41c0-47d1-993b-7ff16b3c1960

-- Generated from ChapterGradedBandSchurEsa.lean — solution of BookProof.GradedBandSchur.degW_pos
import Mathlib
import Definitions.Def_ChapterGradedBandSchurEsaPromoted
import Theorems.Thm_BookProof_GradedBandSchur_degW_ge_one
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
theorem solution (deg : ℕ → ℕ) (k : ℕ) : 0 < degW deg k := lt_of_lt_of_le zero_lt_one (degW_ge_one deg k)
