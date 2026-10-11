-- Prove2me | solution 1 for BookProof.SqueezedGaussStates.opCoef_top
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:57:50.64693+00:00
-- url     : https://prove2.me/submissions/778ac026-49fe-472d-a86f-910e52d3375c

-- Generated from ChapterSqueezedGaussStates.lean — solution of BookProof.SqueezedGaussStates.opCoef_top
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
import Theorems.Thm_BookProof_SqueezedGaussStates_sqCoef_top_succ
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.SqueezedGaussStates




open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (α γ v : ℝ) (M : ℕ) : opCoef α γ v M M = α * sqCoef v M M := by

  rw [opCoef, sqCoef_top_succ]
  ring
