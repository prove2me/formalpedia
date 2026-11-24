-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.appLE_top_comp_topIso_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:36:11.026867+00:00
-- url     : https://prove2.me/submissions/8af92a19-00c4-4c5b-a0e6-605f8da2545b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
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
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Opens)
    (hV : V ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) :
    f.appLE ⊤ V hV ≫ V.topIso.inv = (V.ι ≫ f).appTop := by
  rw [← appTop_comp_topIso_hom f V hV, Category.assoc, Iso.hom_inv_id, Category.comp_id]
end FunctorialResolution.EmbeddedResolution
