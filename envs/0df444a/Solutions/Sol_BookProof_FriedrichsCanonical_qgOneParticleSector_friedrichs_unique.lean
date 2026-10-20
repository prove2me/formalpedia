-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_unique
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T10:37:11.649643+00:00
-- url     : https://prove2.me/submissions/04c449ef-28fd-4bfd-b969-40e31abb50fc

-- Generated from ChapterFriedrichsCanonical.lean — solution of BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_unique
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Theorems.Thm_BookProof_FriedrichsCanonical_semibounded_friedrichs_unique
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
    (V3 : Polynomial ℝ) (c : ℝ) (hV3 : ∀ t : ℝ, -c ≤ V3.eval t)
    {Dom' : Submodule ℂ (L2d 2)} (A' : Dom' →ₗ[ℂ] L2d 2)
    (hA' : IsSemiboundedSelfAdjointExtension c
      (hamCore (scalaronSectorPotential M alpha V3)
        (continuous_scalaronSectorPotential M alpha V3)
        (expBounded_scalaronSectorPotential M alpha hM V3)) A')
    (hform : Dom' ≤ formDomain (qgSectorShiftedPosSymOp M alpha hM halpha V3 c hV3)) :
    Dom' = friedrichsDomain (qgSectorShiftedPosSymOp M alpha hM halpha V3 c hV3) ∧
      ∀ (x : L2d 2) (hx : x ∈ Dom')
        (hx' : x ∈ friedrichsDomain (qgSectorShiftedPosSymOp M alpha hM halpha V3 c hV3)),
        A' ⟨x, hx⟩ = qgSectorFriedrichsOp M alpha hM halpha V3 c hV3 ⟨x, hx'⟩ :=
  semibounded_friedrichs_unique _ (hamCore_symmetricOn _ _ _) c
      (hamCore_quadForm_ge _ _ _ c (scalaronSectorPotential_lower M alpha halpha V3 c hV3))
      polyGaussCore_dense A' hA' hform
