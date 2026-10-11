-- Prove2me | solution 1 for BookProof.ScalaronHermiteEsa.potCore_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:21:32.226632+00:00
-- url     : https://prove2.me/submissions/4855f3bc-9d28-4e12-b13f-d645f8e29f60

-- Generated from ChapterScalaronHermiteEsa.lean — solution of BookProof.ScalaronHermiteEsa.potCore_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Theorems.Thm_BookProof_ScalaronHermiteEsa_potCore_deficiencyTrivialAt
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
open BookProof.ScalaronHermiteEsa




open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {W : Vd d → ℝ} (hWc : Continuous W)
    (hWb : ExpBounded W) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (potCore W hWc hWb) :=
  ⟨potCore_deficiencyTrivialAt hWc hWb (by simp),
      potCore_deficiencyTrivialAt hWc hWb (by simp)⟩
