-- Prove2me | solution 1 for BookProof.YangMillsAbelianNoGap.le_of_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:17:59.014989+00:00
-- url     : https://prove2.me/submissions/23f17490-406e-40fa-bcda-b99490fcf9f1

-- Generated from ChapterYangMillsAbelianNoGap.lean — solution of BookProof.YangMillsAbelianNoGap.le_of_sq_le
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianNoGap
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.YangMillsAbelianNoGap




open MvPolynomial MeasureTheory
open BookProof.HermiteProductCore BookProof.GaussCoordCombo BookProof.SqueezedGaussStates
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.HermiteGalerkin

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable (vf : Fin d → ℝ) (Mf : Fin d → ℕ)

set_option maxHeartbeats 1000000 in
theorem solution {a t b : ℝ} (ht : 0 ≤ t) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ t ^ 2 * b ^ 2) : a ≤ t * b := by

  have h' : a ^ 2 ≤ (t * b) ^ 2 := by rw [mul_pow]; exact h
  exact le_of_sq_le_sq h' (by positivity)
