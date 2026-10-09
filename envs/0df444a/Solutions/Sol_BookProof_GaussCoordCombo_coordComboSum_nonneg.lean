-- Prove2me | solution 1 for BookProof.GaussCoordCombo.coordComboSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:43:35.86799+00:00
-- url     : https://prove2.me/submissions/591e67f8-9ffb-4712-a6b8-c475e33c7306

-- Generated from ChapterGaussCoordCombo.lean — solution of BookProof.GaussCoordCombo.coordComboSum_nonneg
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.GaussCoordCombo




open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (c : ℕ → ℝ) (p K : ℕ) : 0 ≤ coordComboSum c p K := by

  refine Finset.sum_nonneg fun k _ => ?_
  positivity
