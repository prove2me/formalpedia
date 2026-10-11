-- Prove2me | solution 1 for BookProof.SqueezedGaussStates.Vsum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:15:39.45222+00:00
-- url     : https://prove2.me/submissions/e2376d89-9f31-4251-b3e4-29bfcc385fb5

-- Generated from ChapterSqueezedGaussStates.lean — theorem BookProof.SqueezedGaussStates.Vsum_nonneg
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
open BookProof.SqueezedGaussStates



open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}
open BookProof.SqueezedGaussStates

theorem solution(v : ℝ) (M : ℕ) : 0 ≤ Vsum v M := by
  unfold Vsum
  exact Finset.sum_nonneg fun m _ => by unfold Acoef; positivity
