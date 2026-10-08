-- Prove2me | solution 1 for BookProof.FockNumberPreservingGap.shiftCol_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:16:26.707665+00:00
-- url     : https://prove2.me/submissions/065f5e0e-aa94-4a3a-8ea1-ada3c51eb315

-- Generated from ChapterFockNumberPreservingGap.lean — solution of BookProof.FockNumberPreservingGap.shiftCol_apply
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Theorems.Thm_BookProof_FockNumberPreservingGap_numberCol_eq
open BookProof.FockNumberPreservingGap



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution (col : ℕ → (ℕ →₀ ℂ)) (mu : ℝ) (k : ℕ) :
    shiftCol col mu k = col k - ((mu : ℝ) : ℂ) • numberCol k := by

  rw [shiftCol, numberCol_eq]
