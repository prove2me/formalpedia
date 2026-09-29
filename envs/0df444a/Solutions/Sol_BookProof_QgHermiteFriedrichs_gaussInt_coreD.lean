-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.gaussInt_coreD
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:54:55.58937+00:00
-- url     : https://prove2.me/submissions/bdcc7652-5fc3-497f-b20a-da6400832d4b

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.gaussInt_coreD
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_coreD
import Theorems.Thm_BookProof_QgHermiteFriedrichs_gaussInt_coreD_raw
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

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin d) (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (coreD j p) * q) = -gaussInt (cpoly p * coreD j q) := by

  rw [cpoly_coreD, gaussInt_coreD_raw]
