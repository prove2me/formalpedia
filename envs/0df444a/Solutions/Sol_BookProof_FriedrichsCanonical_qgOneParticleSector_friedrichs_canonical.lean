-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_canonical
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T10:37:01.849784+00:00
-- url     : https://prove2.me/submissions/1ca26e6d-8e8b-4f3b-a95f-14acd9ca37e0

-- Generated from ChapterFriedrichsCanonical.lean — solution of BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_canonical
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Theorems.Thm_BookProof_FriedrichsCanonical_semiboundedFriedrichsOp_isSemiboundedSelfAdjointExtension
import Theorems.Thm_BookProof_QgHermiteCore_continuous_scalaronSectorPotential
import Theorems.Thm_BookProof_QgHermiteCore_expBounded_scalaronSectorPotential
import Theorems.Thm_BookProof_QgHermiteFriedrichs_hamCore_quadForm_ge
import Theorems.Thm_BookProof_QgHermiteFriedrichs_hamCore_symmetricOn
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
open BookProof.FriedrichsCanonical




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.HermiteProductCore
open BookProof.QgHermiteCore
open BookProof.QgHermiteFriedrichs

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha)
    (V3 : Polynomial ℝ) (c : ℝ) (hV3 : ∀ t : ℝ, -c ≤ V3.eval t) :
    IsSemiboundedSelfAdjointExtension c
      (hamCore (scalaronSectorPotential M alpha V3)
        (continuous_scalaronSectorPotential M alpha V3)
        (expBounded_scalaronSectorPotential M alpha hM V3))
      (qgSectorFriedrichsOp M alpha hM halpha V3 c hV3) :=
  semiboundedFriedrichsOp_isSemiboundedSelfAdjointExtension _ (hamCore_symmetricOn _ _ _) c
      (hamCore_quadForm_ge _ _ _ c (scalaronSectorPotential_lower M alpha halpha V3 c hV3))
      polyGaussCore_dense
