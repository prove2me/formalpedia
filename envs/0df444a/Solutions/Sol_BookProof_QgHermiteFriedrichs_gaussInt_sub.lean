-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.gaussInt_sub
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T08:00:12.318565+00:00
-- url     : https://prove2.me/submissions/71234d5f-8d83-44ec-8f58-abc13b8441be

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.gaussInt_sub
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
theorem solution (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by

  have h : r - s = r + (-1 : ℂ) • s := by module
  rw [h, gaussInt_add, gaussInt_smul]
  ring
