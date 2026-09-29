-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.expBounded_scalaronW
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:59:37.435946+00:00
-- url     : https://prove2.me/submissions/683732b4-6eb2-489c-81cf-14fd1b20b04e

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.expBounded_scalaronW
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Theorems.Thm_BookProof_QgHermiteCore_ExpBounded_comp_coord
import Theorems.Thm_BookProof_QgHermiteCore_expBounded_starobinskyV
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavine
open BookProof.QgHermiteFriedrichs








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}































variable (W : Vd d → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (hM : 0 < M) : ExpBounded (scalaronW M alpha) := by

  change ExpBounded fun x : Vd 1 => starobinskyV M alpha (x 0)
  exact (expBounded_starobinskyV M alpha hM).comp_coord 0
