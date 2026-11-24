-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.ker_specToAffineSpaceExtendCoords_appTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:49:12.827301+00:00
-- url     : https://prove2.me/submissions/54d005e6-2461-4424-8109-eb900606c752

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_ExtendCoordinatesToAffineSpace
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PolynomialRingOverGlobalSections
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialToSumCoordinateRing_C
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialToSumCoordinateRing_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_specToAffineSpaceExtendCoords_appTop_mvPolynomial
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_homOfSumCoords_appTop_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_homOfSumCoords_appTop_coord_inr
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


attribute [local simp] FunctorialResolution.EmbeddedResolution.mvPolynomialToSumCoordinateRing_C
attribute [local simp] FunctorialResolution.EmbeddedResolution.mvPolynomialToSumCoordinateRing_X
section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem comp_appTop_apply_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (t : Γ(Z, ⊤)) :
    (f ≫ g).appTop t = f.appTop (g.appTop t) := rfl
private theorem id_appTop_apply (X : Scheme.{u}) (t : Γ(X, ⊤)) :
    (𝟙 X : X ⟶ X).appTop t = t := by simp
private theorem appTop_surjective_of_isClosedImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsClosedImmersion f] :
    Function.Surjective ⇑((f.appTop).hom) :=
  (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine (f := f)).2
private theorem appTop_ext {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : ∀ t : Γ(Y, ⊤), f.appTop t = g.appTop t) : f.appTop = g.appTop := by
  ext t
  exact h t
private theorem specMap_appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (f : R ⟶ S) (r : R) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (f r) := by
  have h := congrArg (fun m : R ⟶ Γ(Spec S, ⊤) => CommRingCat.Hom.hom m r)
    (Scheme.ΓSpecIso_inv_naturality f)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h.symm
private theorem globalSectionsToPolynomialRing_apply (k : Type u) [Field k] (M n : ℕ)
    (t : Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    globalSectionsToPolynomialRing k M n t = MvPolynomial.C t := rfl
private theorem comp_affineSpaceIndexedByToSpec_eq (k : Type u) [Field k] (M n : ℕ) :
    specPolynomialRingToAffineSpaceSum k M n ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M ⊕ Fin n)) =
      specHomOfGlobalSections (affineSpaceIndexedBy k (ULift.{u} (Fin M))) (globalSectionsToPolynomialRing k M n) ≫
        affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) :=
  specToAffineSpaceExtendCoords_comp_toSpec k (affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))) M (𝟙 _) (globalSectionsToPolynomialRing k M n) n (polynomialRingVariables k M n)
private theorem appTop_coord_inl_eq_C (k : Type u) [Field k] (M n : ℕ) (a : Fin M) :
    (specPolynomialRingToAffineSpaceSum k M n).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inl a) : ULift.{u} (Fin M ⊕ Fin n))) =
      (Scheme.ΓSpecIso (polynomialRingOverGlobalSections k M n)).inv
        (MvPolynomial.C (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up a))) := by
  have h := specToAffineSpaceExtendCoords_appTop_coord_inl k (affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))) M (𝟙 _) (globalSectionsToPolynomialRing k M n) n (polynomialRingVariables k M n) a
  rw [Category.comp_id, specHomOfGlobalSections_appTop] at h
  exact h
private theorem appTop_coord_inr_eq_X (k : Type u) [Field k] (M n : ℕ) (j : Fin n) :
    (specPolynomialRingToAffineSpaceSum k M n).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (ULift.up (Sum.inr j) : ULift.{u} (Fin M ⊕ Fin n))) =
      (Scheme.ΓSpecIso (polynomialRingOverGlobalSections k M n)).inv (MvPolynomial.X j) :=
  specToAffineSpaceExtendCoords_appTop_coord_inr k (affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))) M (𝟙 _) (globalSectionsToPolynomialRing k M n) n (polynomialRingVariables k M n) j
private theorem appTop_ΓSpecIso_inv_eq_mvPolynomialToSumCoordinateRing (k : Type u) [Field k] (M n : ℕ)
    (r : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤)) :
    (affineSpaceSumToSpecPolynomialRing k M n).appTop ((Scheme.ΓSpecIso (polynomialRingOverGlobalSections k M n)).inv r) =
      mvPolynomialToSumCoordinateRing k M n r := by
  have h1 : (Spec.map (CommRingCat.ofHom (mvPolynomialToSumCoordinateRing k M n))).appTop
        ((Scheme.ΓSpecIso (polynomialRingOverGlobalSections k M n)).inv r) =
      (Scheme.ΓSpecIso Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n)), ⊤)).inv
        (mvPolynomialToSumCoordinateRing k M n r) :=
    specMap_appTop_ΓSpecIso_inv (CommRingCat.ofHom (mvPolynomialToSumCoordinateRing k M n)) r
  have h2 : (affineSpaceSumToSpecPolynomialRing k M n).appTop ((Scheme.ΓSpecIso (polynomialRingOverGlobalSections k M n)).inv r) =
      ((affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n))).isoSpec.hom).appTop
        ((Spec.map (CommRingCat.ofHom (mvPolynomialToSumCoordinateRing k M n))).appTop
          ((Scheme.ΓSpecIso (polynomialRingOverGlobalSections k M n)).inv r)) := rfl
  rw [h2, h1]
  simp [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
private theorem mvPolynomialToSumCoordinateRing_surjective (k : Type u) [Field k] (M n : ℕ) :
    Function.Surjective ⇑(mvPolynomialToSumCoordinateRing k M n) := by
  have hcomp : affineSpaceSumToSpecPolynomialRing k M n ≫ specPolynomialRingToAffineSpaceSum k M n =
      𝟙 (affineSpaceIndexedBy k (ULift.{u} (Fin M ⊕ Fin n))) := by
    refine AffineSpace.hom_ext ?_ ?_
    · apply AlgebraicGeometry.ext_of_isAffine
      apply appTop_ext
      intro t
      rw [Category.assoc, Category.id_comp, comp_affineSpaceIndexedByToSpec_eq, comp_appTop_apply_eq,
        comp_appTop_apply_eq, specHomOfGlobalSections_appTop, globalSectionsToPolynomialRing_apply, appTop_ΓSpecIso_inv_eq_mvPolynomialToSumCoordinateRing,
        mvPolynomialToSumCoordinateRing_C, ← comp_appTop_apply_eq, projLeft_comp_affineSpaceIndexedByToSpec]
    · rintro ⟨i⟩
      obtain a | j := i
      · rw [comp_appTop_apply_eq, appTop_coord_inl_eq_C, appTop_ΓSpecIso_inv_eq_mvPolynomialToSumCoordinateRing, mvPolynomialToSumCoordinateRing_C,
          projLeft_appTop_coord, id_appTop_apply]
      · rw [comp_appTop_apply_eq, appTop_coord_inr_eq_X, appTop_ΓSpecIso_inv_eq_mvPolynomialToSumCoordinateRing, mvPolynomialToSumCoordinateRing_X,
          id_appTop_apply]
  intro x
  refine ⟨(Scheme.ΓSpecIso (polynomialRingOverGlobalSections k M n)).hom ((specPolynomialRingToAffineSpaceSum k M n).appTop x), ?_⟩
  have hx : (affineSpaceSumToSpecPolynomialRing k M n).appTop ((specPolynomialRingToAffineSpaceSum k M n).appTop x) = x := by
    rw [← comp_appTop_apply_eq, hcomp, id_appTop_apply]
  rw [← appTop_ΓSpecIso_inv_eq_mvPolynomialToSumCoordinateRing k M n
    ((Scheme.ΓSpecIso (polynomialRingOverGlobalSections k M n)).hom ((specPolynomialRingToAffineSpaceSum k M n).appTop x)),
    Iso.hom_inv_id_apply]
  exact hx
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
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    [AlgebraicGeometry.IsClosedImmersion e] {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) = pA)
    (q : ℕ) (rel : Fin q → MvPolynomial (Fin n) Γ(A, ⊤))
    (hrel : RingHom.ker (MvPolynomial.eval₂Hom σ.hom b) = Ideal.span (Set.range rel))
    (lift : Fin q → MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤))
    (hlift : ∀ j, MvPolynomial.map (e.appTop).hom (lift j) = rel j) :
    RingHom.ker ((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop).hom =
      Ideal.map ((projLeft k M n).appTop).hom (RingHom.ker (e.appTop).hom)
        ⊔ Ideal.span (Set.range fun j : Fin q => mvPolynomialToSumCoordinateRing k M n (lift j)) := by
  have hsurje : Function.Surjective ⇑((e.appTop).hom) :=
    appTop_surjective_of_isClosedImmersion e
  have hmap : Function.Surjective ⇑(MvPolynomial.map ((e.appTop).hom) :
      MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
        MvPolynomial (Fin n) Γ(A, ⊤)) :=
    MvPolynomial.map_surjective _ hsurje
  have hsurjS : Function.Surjective ⇑(mvPolynomialToSumCoordinateRing k M n) := mvPolynomialToSumCoordinateRing_surjective k M n
  have hι : Function.Injective ⇑((Scheme.ΓSpecIso B').inv) := by
    intro x y hxy
    have h := congrArg (fun z => (Scheme.ΓSpecIso B').hom z) hxy
    simpa using h
  have key : ∀ p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤),
      ((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop).hom (mvPolynomialToSumCoordinateRing k M n p) =
        (Scheme.ΓSpecIso B').inv
          (MvPolynomial.eval₂ σ.hom b (MvPolynomial.map (e.appTop).hom p)) :=
    fun p => specToAffineSpaceExtendCoords_appTop_mvPolynomial k A pA M e σ n b he p
  have step1 : RingHom.ker (((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop).hom.comp
        (mvPolynomialToSumCoordinateRing k M n)) =
      Ideal.comap (MvPolynomial.map ((e.appTop).hom)) (Ideal.span (Set.range rel)) := by
    rw [← hrel]
    ext p
    simp only [RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]
    rw [key p]
    constructor
    · intro h
      have h0 : MvPolynomial.eval₂ σ.hom b (MvPolynomial.map ((e.appTop).hom) p) = 0 := by
        apply hι
        rw [h]
        simp
      simpa [RingHom.mem_ker] using h0
    · intro h
      have h0 : MvPolynomial.eval₂ σ.hom b (MvPolynomial.map ((e.appTop).hom) p) = 0 := by
        simpa [RingHom.mem_ker] using h
      rw [h0]
      simp
  have step2 : Ideal.span (Set.range rel) =
      Ideal.map (MvPolynomial.map ((e.appTop).hom)) (Ideal.span (Set.range lift)) := by
    rw [Ideal.map_span]
    congr 1
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun j => (hlift j).symm)
  have step3 : Ideal.comap (MvPolynomial.map ((e.appTop).hom))
        (Ideal.map (MvPolynomial.map ((e.appTop).hom)) (Ideal.span (Set.range lift))) =
      Ideal.span (Set.range lift) ⊔
        RingHom.ker (MvPolynomial.map ((e.appTop).hom) :
          MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
            MvPolynomial (Fin n) Γ(A, ⊤)) :=
    Ideal.comap_map_of_surjective _ hmap _
  have step4 : RingHom.ker (MvPolynomial.map ((e.appTop).hom) :
        MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
          MvPolynomial (Fin n) Γ(A, ⊤)) =
      Ideal.map
        (MvPolynomial.C :
          Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
            MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤))
        (RingHom.ker ((e.appTop).hom)) :=
    MvPolynomial.ker_map _
  have hcomapker : Ideal.comap (mvPolynomialToSumCoordinateRing k M n)
        (RingHom.ker ((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop).hom) =
      RingHom.ker (((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop).hom.comp (mvPolynomialToSumCoordinateRing k M n)) := by
    ext p
    simp [RingHom.mem_ker, Ideal.mem_comap]
  have hcompEq : (mvPolynomialToSumCoordinateRing k M n).comp
      (MvPolynomial.C :
        Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤) →+*
          MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤))
      = ((projLeft k M n).appTop).hom := by
    ext t
    exact mvPolynomialToSumCoordinateRing_C k M n t
  have main := Ideal.map_comap_of_surjective (mvPolynomialToSumCoordinateRing k M n) hsurjS
    (RingHom.ker ((specToAffineSpaceExtendCoords k A pA M e σ n b).appTop).hom)
  rw [hcomapker, step1, step2, step3, step4] at main
  rw [← main, Ideal.map_sup, Ideal.map_span, Ideal.map_map, hcompEq]
  have hrange : (⇑(mvPolynomialToSumCoordinateRing k M n) '' Set.range lift)
      = Set.range (fun j : Fin q => mvPolynomialToSumCoordinateRing k M n (lift j)) := by
    rw [← Set.range_comp]
    rfl
  rw [hrange, sup_comm]
end FunctorialResolution.EmbeddedResolution
