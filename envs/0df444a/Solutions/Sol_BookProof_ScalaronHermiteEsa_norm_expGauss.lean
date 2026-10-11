-- Prove2me | solution 1 for BookProof.ScalaronHermiteEsa.norm_expGauss
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:18:56.089008+00:00
-- url     : https://prove2.me/submissions/9627371d-a242-4887-99ed-6b3837d364a8

-- Generated from ChapterScalaronHermiteEsa.lean — solution of BookProof.ScalaronHermiteEsa.norm_expGauss
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
open BookProof.ScalaronHermiteEsa




open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (c : ℝ) (x : Vd d) :
    ‖((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ)‖ = Real.exp (c * ‖x‖) * gaussD x := by

  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_pos (Real.exp_pos _) (gaussD_pos x)).le]
