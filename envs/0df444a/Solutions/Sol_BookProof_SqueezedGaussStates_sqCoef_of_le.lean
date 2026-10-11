-- Prove2me | solution 1 for BookProof.SqueezedGaussStates.sqCoef_of_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:44.42021+00:00
-- url     : https://prove2.me/submissions/82fcb741-4f81-4b41-a382-850674d46d39

-- Generated from ChapterSqueezedGaussStates.lean — solution of BookProof.SqueezedGaussStates.sqCoef_of_le
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.SqueezedGaussStates




open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {v : ℝ} {M m : ℕ} (h : m ≤ M) :
    sqCoef v M m = v ^ m / (m.factorial : ℝ) := if_pos h
