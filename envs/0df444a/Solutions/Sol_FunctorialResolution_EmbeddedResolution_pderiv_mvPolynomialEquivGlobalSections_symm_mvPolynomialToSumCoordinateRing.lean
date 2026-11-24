-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.pderiv_mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:54:07.083854+00:00
-- url     : https://prove2.me/submissions/012b9681-a148-4f9b-b144-d7f9fd1e0245

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pderiv_inr_renameSumInl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing
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
private theorem pderiv_inr_eval₂_X_inr (k : Type u) [Field k] (M n : ℕ)
    (f : Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
      MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k) (i : Fin n)
    (hf : ∀ t, MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n)) (f t) = 0)
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.eval₂ f
          (fun j : Fin n =>
            MvPolynomial.X (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n))) p) =
      MvPolynomial.eval₂ f
        (fun j : Fin n =>
          MvPolynomial.X (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n)))
        (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on
  · rename_i t
    rw [MvPolynomial.eval₂_C, MvPolynomial.pderiv_C, MvPolynomial.eval₂_zero]
    exact hf t
  · rename_i q r hq hr
    simp [MvPolynomial.eval₂_add, hq, hr]
  · rename_i q j hq
    have hX : MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        (MvPolynomial.X (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n)) :
          MvPolynomial (ULift.{u} (Fin M ⊕ Fin n)) k) =
        MvPolynomial.eval₂ f
          (fun l : Fin n =>
            MvPolynomial.X (ULift.up (Sum.inr l) : ULift.{u} (Fin M ⊕ Fin n)))
          (MvPolynomial.pderiv i (MvPolynomial.X j)) := by
      by_cases h : i = j
      · subst h
        simp
      · simp [MvPolynomial.pderiv_X, h]
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.pderiv_mul,
      MvPolynomial.eval₂_add, hq, hX]
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
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    MvPolynomial.pderiv (ULift.up (Sum.inr i) : ULift.{u} (Fin M ⊕ Fin n))
        ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm (mvPolynomialToSumCoordinateRing k M n p)) =
      (mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M ⊕ Fin n))).symm
        (mvPolynomialToSumCoordinateRing k M n (MvPolynomial.pderiv i p)) := by
  rw [mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing, mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing]
  refine pderiv_inr_eval₂_X_inr k M n
    ((renameSumInl k M n).comp ((mvPolynomialEquivGlobalSections k (ULift.{u} (Fin M))).symm.toRingHom)) i ?_ p
  intro t
  rw [RingHom.comp_apply]
  exact pderiv_inr_renameSumInl k M n i _
end FunctorialResolution.EmbeddedResolution
