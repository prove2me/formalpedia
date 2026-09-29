-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.continuous_scalaronW
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:57:54.650302+00:00
-- url     : https://prove2.me/submissions/2cebf7fc-3dcd-42c4-9e65-efb13c3f2874

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.continuous_scalaronW
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Theorems.Thm_BookProof_QgHermiteCore_continuous_starobinskyV
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
theorem solution (M alpha : ℝ) : Continuous (scalaronW M alpha) := by

  change Continuous fun x : Vd 1 => starobinskyV M alpha (x 0)
  exact (continuous_starobinskyV M alpha).comp (by fun_prop)
