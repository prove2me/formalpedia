-- Prove2me | solution 1 for BookProof.SqueezedGaussStates.Usum_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:57:55.214171+00:00
-- url     : https://prove2.me/submissions/2b742dbb-7c3f-4486-9053-fb8c092f6519

-- Generated from ChapterSqueezedGaussStates.lean — solution of BookProof.SqueezedGaussStates.Usum_le
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
import Theorems.Thm_BookProof_SqueezedGaussStates_Acoef_nonneg
import Theorems.Thm_BookProof_SqueezedGaussStates_Usum_identity
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.SqueezedGaussStates




open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (v : ℝ) (M : ℕ) :
    (1 - 4 * v ^ 2) * Usum v M ≤ Vsum v M := by

  have h := Usum_identity v M
  have hA : 0 ≤ 4 * v ^ 2 * (2 * (M : ℝ) + 1) * Acoef v M := by
    have := Acoef_nonneg v M
    positivity
  linarith
