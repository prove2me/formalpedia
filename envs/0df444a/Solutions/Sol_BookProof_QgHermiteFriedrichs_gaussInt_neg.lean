-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.gaussInt_neg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:59:54.897729+00:00
-- url     : https://prove2.me/submissions/60f70b6f-992c-4473-ae9c-9688e4018111

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.gaussInt_neg
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavine
open BookProof.QgHermiteFriedrichs








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (r : MvPolynomial (Fin d) ℂ) : gaussInt (-r) = -gaussInt r := by

  have h : -r = (-1 : ℂ) • r := by module
  rw [h, gaussInt_smul]
  ring
