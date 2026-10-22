-- Prove2me | solution 1 for BookProof.FockCubicQuarticStability.dGamma_cubic_quartic_bounded_below
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:12:18.479269+00:00
-- url     : https://prove2.me/submissions/b5daede4-95d0-45cc-b63f-c270021877d5

-- Generated from ChapterFockCubicQuarticStability.lean — solution of BookProof.FockCubicQuarticStability.dGamma_cubic_quartic_bounded_below
import Mathlib
import Definitions.Def_ChapterFockCubicQuarticStability
import Theorems.Thm_BookProof_FockCubicQuarticStability_numberForm_cubic_quartic_bounded_below
import Theorems.Thm_BookProof_FockFieldPerturbation_number_le_dGamma_quadForm
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
theorem solution (k : ℕ) {col : ℕ → (ℕ →₀ ℂ)} {mu lam : ℝ}
    (hmu : 0 < mu) (hgap : IsPosCol (shiftCol col mu)) (u : FockAlg) :
    -(2 * lam ^ 2 + (2 * lam ^ 2 + 1 / 2 - mu) ^ 2 / 2) * ‖toLp u‖ ^ 2
      ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re
        + lam * (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re
        + (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re := by

  have hbase := numberForm_cubic_quartic_bounded_below k (mu := mu) (lam := lam) hmu.le u
  have hfree : mu * numberQuad u ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re :=
    number_le_dGamma_quadForm hgap u
  linarith
