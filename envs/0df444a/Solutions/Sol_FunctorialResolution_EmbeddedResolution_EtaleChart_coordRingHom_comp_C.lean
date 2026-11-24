-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_comp_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:56:05.564821+00:00
-- url     : https://prove2.me/submissions/2d3ecc8b-10f5-40cf-bd52-06ec87ceb210

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_AlgebraicGeometry_Scheme_presheaf_map_eq_of_parallel
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem comp_presheafMap_comp_presheafMap {X₁ : Scheme.{u}} {R : CommRingCat.{u}}
    {A B C : (X₁.Opens)ᵒᵖ} (h : R ⟶ X₁.presheaf.obj A) (g₁ : A ⟶ B) (g₂ : B ⟶ C) (g₃ : A ⟶ C) :
    (h ≫ X₁.presheaf.map g₁) ≫ X₁.presheaf.map g₂ = h ≫ X₁.presheaf.map g₃ := by
  rw [Category.assoc, ← Functor.map_comp, Scheme.presheaf_map_eq_of_parallel X₁ (g₁ ≫ g₂) g₃]
private theorem appTop_comp_topIso_hom {X₁ Y₁ : Scheme.{u}} (f : X₁ ⟶ Y₁) (V : X₁.Opens)
    (hV : V ≤ f ⁻¹ᵁ (⊤ : Y₁.Opens)) :
    (V.ι ≫ f).appTop ≫ V.topIso.hom = f.appLE ⊤ V hV := by
  have hR : f.appLE ⊤ V hV = f.app ⊤ ≫ X₁.presheaf.map (homOfLE hV).op := rfl
  simp
  rw [hR]
  exact comp_presheafMap_comp_presheafMap _ _ _ _
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
private theorem affineSpace_specIso_hom_comp_specMap_C (K : Type u) [Field K] (n : ℕ) :
    (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).hom ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin n)) K)) =
      affineSpaceFinToSpec K n := by
  have h : (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).inv ≫
      affineSpaceFinToSpec K n =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin n)) K)) := by
    simp
  rw [← h, Iso.hom_inv_id_assoc]
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleChart
theorem _root_.solution (c : EtaleChart p U m) :
    c.coordRingHom.comp (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k) =
      sectionsAlgebraMap k p U := by
  have hC : CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k))).appTop :=
    Scheme.ΓSpecIso_inv_naturality _
  have key : CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv ≫
          (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop ≫
            c.map.appTop ≫ U.topIso.hom =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U) := by
    rw [← Category.assoc, hC, Category.assoc,
      ← Category.assoc _ _ (c.map.appTop ≫ U.topIso.hom), ← Scheme.Hom.comp_appTop,
      affineSpace_specIso_hom_comp_specMap_C k m, ← Category.assoc _ _ U.topIso.hom,
      ← Scheme.Hom.comp_appTop, c.comp_struct, appTop_comp_topIso_hom p U (le_preimage_top k p U)]
  have h := congrArg CommRingCat.Hom.hom key
  exact RingHom.ext fun x => DFunLike.congr_fun h x
end EtaleChart
end FunctorialResolution.EmbeddedResolution
