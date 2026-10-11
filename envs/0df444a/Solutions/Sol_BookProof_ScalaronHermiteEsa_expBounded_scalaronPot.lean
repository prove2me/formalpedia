-- Prove2me | solution 1 for BookProof.ScalaronHermiteEsa.expBounded_scalaronPot
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:21:33.31801+00:00
-- url     : https://prove2.me/submissions/1dc88aca-ff63-492f-8c81-6dbb7eb42617

-- Generated from ChapterScalaronHermiteEsa.lean — solution of BookProof.ScalaronHermiteEsa.expBounded_scalaronPot
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Theorems.Thm_BookProof_QgHermiteCore_ExpBounded_comp_coord
import Theorems.Thm_BookProof_QgHermiteCore_expBounded_starobinskyV
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.ScalaronHermiteEsa




open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (hM : 0 < M) : ExpBounded (scalaronPot M alpha) := (expBounded_starobinskyV M alpha hM).comp_coord 0
