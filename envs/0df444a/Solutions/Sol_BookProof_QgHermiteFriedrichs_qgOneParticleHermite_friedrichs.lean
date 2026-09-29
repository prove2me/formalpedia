-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.qgOneParticleHermite_friedrichs
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:45:24.312241+00:00
-- url     : https://prove2.me/submissions/c47c2600-3925-41ad-8c41-07f525975dac

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.qgOneParticleHermite_friedrichs
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Theorems.Thm_BookProof_QgHermiteFriedrichs_hermiteCore_friedrichs_extension_of_nonneg
import Theorems.Thm_BookProof_QgHermiteFriedrichs_continuous_scalaronW
import Theorems.Thm_BookProof_QgHermiteFriedrichs_expBounded_scalaronW
import Theorems.Thm_BookProof_QgHermiteFriedrichs_scalaronW_nonneg
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
theorem solution (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) :
    ∃ (Dom : Submodule ℂ (L2d 1)) (A : Dom →ₗ[ℂ] L2d 1),
      IsPositiveSelfAdjointExtension
        (hamCore (scalaronW M alpha) (continuous_scalaronW M alpha)
          (expBounded_scalaronW M alpha hM)) A := hermiteCore_friedrichs_extension_of_nonneg _ _ _ (scalaronW_nonneg halpha)
