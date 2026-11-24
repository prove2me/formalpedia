-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.appTop_specToAffineSpaceExtendCoords_jacobianDetSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:16:55.005724+00:00
-- url     : https://prove2.me/submissions/7360c811-9fc5-40fc-9a74-6756d35a50b6

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_ExtendCoordinatesToAffineSpace
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphChart
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphChartSmooth
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PolynomialRingOverGlobalSections
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceGlobalSections
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SmoothAffinePullbackPresentation
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SumCoordinatePartialDerivatives
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SmoothPullbackGraphChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphPreSubmersivePresentation_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphPreSubmersivePresentation_relation
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_homOfSumCoords_appTop_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_homOfSumCoords_appTop_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_jacobianMatrixOfSections_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_symm_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialToSumCoordinateRing_C
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialToSumCoordinateRing_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pderiv_mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_projLeft_appTop_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_projLeft_comp_affineSpaceIndexedByToSpec
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_projRight_appTop_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_projRight_comp_affineSpaceIndexedByToSpec
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_specHomOfGlobalSections_appTop
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_specToAffineSpaceExtendCoords_appTop_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_specToAffineSpaceExtendCoords_appTop_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_specToAffineSpaceExtendCoords_appTop_mvPolynomial
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
attribute [local simp] FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_relation
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
private theorem jacobianDetSection_mvPolynomialToSumCoordinateRing (k : Type u) [Field k] (M n q : ℕ)
    (lift : Fin q → MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)), ⊤))
    (s : Fin q → Fin n) :
    jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s =
      mvPolynomialToSumCoordinateRing k M n
        (Matrix.det (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (lift j))) := by
  have key : ∀ i j : Fin q,
      jacobianMatrixOfSections k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s i j =
        (mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))).symm
          (mvPolynomialToSumCoordinateRing k M n (MvPolynomial.pderiv (s i) (lift j))) := by
    intro i j
    have h0 : polynomialOfSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) j
        = (mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))).symm (mvPolynomialToSumCoordinateRing k M n (lift j)) := rfl
    rw [jacobianMatrixOfSections_apply, h0]
    exact pderiv_mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing k M n (s i) (lift j)
  have hmat : jacobianMatrixOfSections k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s =
      ((((mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))).symm.toRingHom).comp
          (mvPolynomialToSumCoordinateRing k M n)).mapMatrix)
        (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (lift j)) := by
    refine Matrix.ext fun i j => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, RingHom.coe_comp,
      Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    exact key i j
  show mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))
      (jacobianMatrixOfSections k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s).det = _
  rw [hmat, ← RingHom.map_det]
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
theorem _root_.solution (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)))
    [AlgebraicGeometry.IsClosedImmersion e] {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n q : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) = pA)
    (rel : Fin q → MvPolynomial (Fin n) Γ(A, ⊤))
    (lift : Fin q → MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)), ⊤))
    (hlift : ∀ j, MvPolynomial.map (e.appTop).hom (lift j) = rel j)
    (s : Fin q → Fin n) :
    (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop
        (jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s) =
      (Scheme.ΓSpecIso B').inv
        (Matrix.det (Matrix.of fun i j : Fin q =>
          MvPolynomial.eval₂ σ.hom b ((MvPolynomial.pderiv (s i)) (rel j)))) := by
  have hmap : ∀ i j : Fin q,
      (MvPolynomial.map (CommRingCat.Hom.hom (Scheme.Hom.appTop e)))
          (MvPolynomial.pderiv (s i) (lift j)) = MvPolynomial.pderiv (s i) (rel j) := by
    intro i j
    rw [← MvPolynomial.pderiv_map, hlift j]
  have hM1 : ((MvPolynomial.map (CommRingCat.Hom.hom (Scheme.Hom.appTop e))).mapMatrix
        (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (lift j)))
      = Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (rel j) := by
    refine Matrix.ext fun i j => ?_
    simpa [RingHom.mapMatrix_apply] using hmap i j
  have hM2 : ((MvPolynomial.eval₂Hom (CommRingCat.Hom.hom σ) b).mapMatrix
        (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (rel j)))
      = Matrix.of fun i j : Fin q =>
          MvPolynomial.eval₂ (CommRingCat.Hom.hom σ) b (MvPolynomial.pderiv (s i) (rel j)) := by
    refine Matrix.ext fun i j => ?_
    simp [RingHom.mapMatrix_apply]
  rw [jacobianDetSection_mvPolynomialToSumCoordinateRing k M n q lift s,
    specToAffineSpaceExtendCoords_appTop_mvPolynomial k A pA M e σ n b he]
  congr 1
  rw [RingHom.map_det, hM1]
  show (MvPolynomial.eval₂Hom (CommRingCat.Hom.hom σ) b)
      (Matrix.det (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (rel j))) = _
  rw [RingHom.map_det, hM2]
end FunctorialResolution.EmbeddedResolution
