-- Prove2me | solution 1 for BookProof.YangMillsAbelianNoGap.norm_pgLp_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:07:39.745231+00:00
-- url     : https://prove2.me/submissions/905db24c-aba3-42ab-9c31-cc2ffec6accc

-- Generated from ChapterYangMillsAbelianNoGap.lean — solution of BookProof.YangMillsAbelianNoGap.norm_pgLp_sq
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianNoGap
import Theorems.Thm_BookProof_YangMillsHermite_inner_pgLp_pgLp
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsAbelianNoGap




open MvPolynomial MeasureTheory
open BookProof.HermiteProductCore BookProof.GaussCoordCombo BookProof.SqueezedGaussStates
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.HermiteGalerkin

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {q : MvPolynomial (Fin d) ℂ} (hq : RealCoeff q) {r : ℝ}
    (h : gaussInt (q * q) = ((r : ℝ) : ℂ)) : ‖pgLp q‖ ^ 2 = r := by

  have hinner : (inner ℂ (pgLp q) (pgLp q) : ℂ) = gaussInt (starP q * q) := inner_pgLp_pgLp q q
  rw [show starP q = q from hq, h] at hinner
  have hnorm : (inner ℂ (pgLp q) (pgLp q) : ℂ) = ((‖pgLp q‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hnorm] at hinner
  exact_mod_cast hinner
