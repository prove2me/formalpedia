-- Prove2me | solution 1 for BookProof.SqueezedGaussStates.Vsum_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:11:44.692563+00:00
-- url     : https://prove2.me/submissions/20e263ff-4d3e-49d0-95d8-992b7b571ee6

-- Generated from ChapterSqueezedGaussStates.lean — theorem BookProof.SqueezedGaussStates.Vsum_ge_one
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
open BookProof.SqueezedGaussStates



open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}
open BookProof.SqueezedGaussStates

theorem solution(v : ℝ) (M : ℕ) : 1 ≤ Vsum v M := by
  unfold Vsum
  rw [Finset.sum_range_succ']
  have h0 : Acoef v 0 = 1 := by simp [Acoef]
  rw [h0]
  have : 0 ≤ ∑ i ∈ Finset.range M, Acoef v (i + 1) :=
    Finset.sum_nonneg fun i _ => by unfold Acoef; positivity
  linarith
