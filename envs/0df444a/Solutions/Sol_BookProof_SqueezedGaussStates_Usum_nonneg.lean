-- Prove2me | solution 1 for BookProof.SqueezedGaussStates.Usum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:15:36.435647+00:00
-- url     : https://prove2.me/submissions/2fd68ff7-e9b4-4193-aad2-281f447e6427

-- Generated from ChapterSqueezedGaussStates.lean — theorem BookProof.SqueezedGaussStates.Usum_nonneg
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
open BookProof.SqueezedGaussStates



open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}
open BookProof.SqueezedGaussStates

theorem solution(v : ℝ) (M : ℕ) : 0 ≤ Usum v M := by
  unfold Usum
  exact Finset.sum_nonneg fun m _ => by unfold Acoef; positivity
