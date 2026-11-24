-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_symm_projLeft_appTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:03:58.645221+00:00
-- url     : https://prove2.me/submissions/6e5863c0-71b7-497c-9f29-be7c1a42dac6

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_homOfSumCoords_appTop_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_homOfSumCoords_appTop_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_C
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
private theorem projLeft_appTop_affineSpaceIndexedByToSpec_appTop (k : Type u) [Field k] (M n : ℕ)
    (y : Γ(Spec (CommRingCat.of k), ⊤)) :
    (projLeft k M n).appTop ((affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))).appTop y) =
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M ⊕ Fin n))).appTop y := by
  have h2 : ((projLeft k M n) ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))).appTop y
      = (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M ⊕ Fin n))).appTop y := by
    rw [projLeft_comp_affineSpaceIndexedByToSpec]
  exact h2
private theorem projLeft_appTop_mvPolynomialEquivGlobalSections_C (k : Type u) [Field k] (M n : ℕ) (c : k) :
    (projLeft k M n).appTop (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.C c)) =
      mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n)) (MvPolynomial.C c) := by
  rw [mvPolynomialEquivGlobalSections_C, mvPolynomialEquivGlobalSections_C, projLeft_appTop_affineSpaceIndexedByToSpec_appTop]
private theorem projLeft_appTop_mvPolynomialEquivGlobalSections_X (k : Type u) [Field k] (M n : ℕ)
    (a : ULift.{u} (Fin M)) :
    (projLeft k M n).appTop (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.X a)) =
      mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.X (ULift.up (Sum.inl a.down) : ULift.{u} (Fin M ⊕ Fin n))) := by
  obtain ⟨a⟩ := a
  simp
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (M n : ℕ)
    (p : MvPolynomial (ULift.{u} (Fin M)) k) :
    (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
        ((projLeft k M n).appTop (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) p)) =
      renameSumInl k M n p := by
  have key :
      ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm.toRingHom).comp
          ((((projLeft k M n).appTop).hom).comp
            ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).toRingHom))
        = renameSumInl k M n := by
    apply MvPolynomial.ringHom_ext
    · intro c
      show (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
          ((projLeft k M n).appTop
            (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.C c)))
          = renameSumInl k M n (MvPolynomial.C c)
      rw [projLeft_appTop_mvPolynomialEquivGlobalSections_C, RingEquiv.symm_apply_apply, renameSumInl_C]
    · intro a
      show (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
          ((projLeft k M n).appTop
            (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M)) (MvPolynomial.X a)))
          = renameSumInl k M n (MvPolynomial.X a)
      rw [projLeft_appTop_mvPolynomialEquivGlobalSections_X, RingEquiv.symm_apply_apply]
      simp [renameSumInl]
  exact RingHom.congr_fun key p
end FunctorialResolution.EmbeddedResolution
