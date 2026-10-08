-- Prove2me | solution 1 for BookProof.ScalaronHermiteEsa.continuous_scalaronPot
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T11:01:25.118451+00:00
-- url     : https://prove2.me/submissions/79188b20-fcb0-4f9b-8f48-8706ae5a0aa3

-- Generated from ChapterScalaronHermiteEsa.lean — solution of BookProof.ScalaronHermiteEsa.continuous_scalaronPot
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Theorems.Thm_BookProof_QgHermiteCore_continuous_starobinskyV
open BookProof.ScalaronHermiteEsa




open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) : Continuous (scalaronPot M alpha) := (continuous_starobinskyV M alpha).comp (by fun_prop)
