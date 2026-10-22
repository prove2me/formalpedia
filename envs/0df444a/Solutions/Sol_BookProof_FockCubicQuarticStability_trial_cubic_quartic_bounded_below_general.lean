-- Prove2me | solution 1 for BookProof.FockCubicQuarticStability.trial_cubic_quartic_bounded_below_general
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:12:06.446424+00:00
-- url     : https://prove2.me/submissions/24b548d5-ec5c-47f3-883b-1ec599f411e7

-- Generated from ChapterFockCubicQuarticStability.lean — solution of BookProof.FockCubicQuarticStability.trial_cubic_quartic_bounded_below_general
import Mathlib
import Definitions.Def_ChapterFockCubicQuarticStability
import Theorems.Thm_BookProof_FockCubicQuarticStability_numberForm_cubic_quartic_bounded_below
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockCubicQuarticStability



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockCubicUnbounded
open BookProof.FockSecondQuantization

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (lam : ℝ) (u : FockAlg) :
    -(2 * lam ^ 4 + lam ^ 2 + 1 / 8) * ‖toLp u‖ ^ 2
      ≤ numberQuad u
        + lam * (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re
        + (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re := by

  have h := numberForm_cubic_quartic_bounded_below k (mu := 1) (lam := lam) zero_le_one u
  have hconst : (2 * lam ^ 2 + (2 * lam ^ 2 + 1 / 2 - 1) ^ 2 / 2)
      = 2 * lam ^ 4 + lam ^ 2 + 1 / 8 := by ring
  rw [hconst] at h
  simpa using h
