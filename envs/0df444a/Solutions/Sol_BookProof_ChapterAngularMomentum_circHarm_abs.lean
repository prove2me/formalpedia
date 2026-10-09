-- Prove2me | solution 1 for BookProof.ChapterAngularMomentum.circHarm_abs
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:37:41.34818+00:00
-- url     : https://prove2.me/submissions/c4ac69be-f0f0-4ef6-bda6-753b95d2514f

-- Generated from ChapterAngularMomentum.lean — solution of BookProof.ChapterAngularMomentum.circHarm_abs
import Mathlib
import Definitions.Def_ChapterAngularMomentum
open BookProof.ChapterAngularMomentum




open Complex

set_option maxHeartbeats 1000000 in
theorem solution {μ : ℕ} {z : ℂ} (hz : z ≠ 0) : ‖circHarm μ z‖ = 1 := by

  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [circHarm, norm_pow, norm_div]
  simp [hnz]
