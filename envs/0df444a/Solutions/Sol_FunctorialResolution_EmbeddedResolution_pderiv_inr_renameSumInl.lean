-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.pderiv_inr_renameSumInl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:05:33.915607+00:00
-- url     : https://prove2.me/submissions/b81b5e33-ed1c-4062-91fe-d5c1a37418ee

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PolynomialRingOverGlobalSections
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceGlobalSections
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SumCoordinatePartialDerivatives
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_renameSumInl_C
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_renameSumInl_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_homOfSumCoords_appTop_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_homOfSumCoords_appTop_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_symm_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialToSumCoordinateRing_C
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialToSumCoordinateRing_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_projLeft_appTop_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_projLeft_comp_affineSpaceIndexedByToSpec
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_projRight_appTop_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_projRight_comp_affineSpaceIndexedByToSpec
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_specHomOfGlobalSections_appTop
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_specToAffineSpaceExtendCoords_appTop_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_specToAffineSpaceExtendCoords_appTop_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_specToAffineSpaceExtendCoords_comp_toSpec
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sumUliftEquivUliftSum_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sumUliftEquivUliftSum_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sumUliftEquivUliftSum_symm_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sumUliftEquivUliftSum_symm_inr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.homOfSumCoords_appTop_coord_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.homOfSumCoords_appTop_coord_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_symm_coord
attribute [local simp] FunctorialResolution.EmbeddedResolution.mvPolynomialToSumCoordinateRing_C
attribute [local simp] FunctorialResolution.EmbeddedResolution.mvPolynomialToSumCoordinateRing_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.projLeft_appTop_coord
attribute [local simp] FunctorialResolution.EmbeddedResolution.projLeft_comp_affineSpaceIndexedByToSpec
attribute [local simp] FunctorialResolution.EmbeddedResolution.projRight_appTop_coord
attribute [local simp] FunctorialResolution.EmbeddedResolution.projRight_comp_affineSpaceIndexedByToSpec
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def
attribute [local simp] FunctorialResolution.EmbeddedResolution.specHomOfGlobalSections_appTop
attribute [local simp] FunctorialResolution.EmbeddedResolution.specToAffineSpaceExtendCoords_appTop_coord_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.specToAffineSpaceExtendCoords_appTop_coord_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.specToAffineSpaceExtendCoords_comp_toSpec
attribute [local simp] FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_symm_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_symm_inr


section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem pderiv_inr_X_inl (k : Type u) [Field k] (M n : ℕ) (i : Fin n) (a : Fin M) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.X (ULift.up (Sum.inl a) : ULift.{u} (Fin M ⊕ Fin n)) :
          MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k) = 0 := by
  classical
  simp [MvPolynomial.pderiv_X]
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (M n : ℕ) (i : Fin n)
    (p : MvPolynomial (ULift.{u} (Fin M)) k) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (renameSumInl k M n p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on
  · rename_i c
    simp [renameSumInl_C]
  · rename_i q r hq hr
    simp [hq, hr]
  · rename_i q a hq
    obtain ⟨a⟩ := a
    rw [map_mul, renameSumInl_X, MvPolynomial.pderiv_mul, hq, pderiv_inr_X_inl]
    simp
end FunctorialResolution.EmbeddedResolution
