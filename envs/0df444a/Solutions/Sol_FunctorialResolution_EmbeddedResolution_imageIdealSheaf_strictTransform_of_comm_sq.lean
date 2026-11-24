-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.imageIdealSheaf_strictTransform_of_comm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:49:01.737189+00:00
-- url     : https://prove2.me/submissions/b2d5fdba-46b9-4f5a-8e5f-98b65bb25c73

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_eq_comap_inv
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_comap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ker_comp_eq_imageIdealSheaf_ker
import Theorems.Thm_FunctorialResolution_Blowup_strictTransformImmersion_eq
import Theorems.Thm_FunctorialResolution_Blowup_strictTransformOpens_eq
import Theorems.Thm_FunctorialResolution_Blowup_strictTransform_eq_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem exists_iso_subscheme_comap_of_isIso {A B : Scheme.{u}} (w : A ⟶ B) [IsIso w]
    (I : B.IdealSheafData) :
    ∃ θ : (I.comap w).subscheme ≅ I.subscheme,
      θ.hom ≫ I.subschemeι = (I.comap w).subschemeι ≫ w := by
  have e1 : ((I.comap w).subschemeι ≫ w).ker = I := by
    rw [ker_comp_eq_imageIdealSheaf_ker, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι,
      imageIdealSheaf_comap]
  have e2 : (I.subschemeι ≫ inv w).ker = I.comap w := by
    rw [ker_comp_eq_imageIdealSheaf_ker, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι,
      imageIdealSheaf_eq_comap_inv, IsIso.inv_inv]
  have h1 : I.subschemeι.ker ≤ ((I.comap w).subschemeι ≫ w).ker :=
    le_of_eq (by rw [e1, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι])
  have h2 : (I.comap w).subschemeι.ker ≤ (I.subschemeι ≫ inv w).ker :=
    le_of_eq (by rw [e2, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι])
  refine ⟨⟨IsClosedImmersion.lift I.subschemeι ((I.comap w).subschemeι ≫ w) h1,
    IsClosedImmersion.lift (I.comap w).subschemeι (I.subschemeι ≫ inv w) h2, ?_, ?_⟩, ?_⟩
  · rw [← cancel_mono (I.comap w).subschemeι, Category.assoc, IsClosedImmersion.lift_fac,
      ← Category.assoc, IsClosedImmersion.lift_fac, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · rw [← cancel_mono I.subschemeι, Category.assoc, IsClosedImmersion.lift_fac,
      ← Category.assoc, IsClosedImmersion.lift_fac, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, Category.id_comp]
  · exact IsClosedImmersion.lift_fac ..
private theorem compl_support_comap {A B : Scheme.{u}} (v : A ⟶ B) (I : B.IdealSheafData) :
    (I.comap v).support.compl = (TopologicalSpace.Opens.map v.base).obj I.support.compl := by
  ext x
  simp [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
private theorem opens_map_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (U : C.Opens) :
    (TopologicalSpace.Opens.map (f ≫ g).base).obj U
      = (TopologicalSpace.Opens.map f.base).obj ((TopologicalSpace.Opens.map g.base).obj U) := by
  ext x
  simp
private theorem opens_map_id {B : Scheme.{u}} (W : B.Opens) :
    (TopologicalSpace.Opens.map (𝟙 B : B ⟶ B).base).obj W = W := by
  ext x
  exact Iff.rfl
private theorem exists_iso_opens_preimage {A B : Scheme.{u}} (θ : A ≅ B) (V' : A.Opens) (V : B.Opens)
    (hVV' : V' = (TopologicalSpace.Opens.map θ.hom.base).obj V) :
    ∃ c : (↑V' : Scheme.{u}) ≅ (↑V : Scheme.{u}), c.hom ≫ V.ι = V'.ι ≫ θ.hom := by
  have hcomp : (TopologicalSpace.Opens.map θ.inv.base).obj V'
      = (TopologicalSpace.Opens.map (θ.inv ≫ θ.hom).base).obj V := by
    rw [hVV', opens_map_comp]
  have hle : V ≤ (TopologicalSpace.Opens.map θ.inv.base).obj V' :=
    le_of_eq (by rw [hcomp, Iso.inv_hom_id, opens_map_id])
  refine ⟨⟨Scheme.Hom.resLE θ.hom V V' (le_of_eq hVV'),
    Scheme.Hom.resLE θ.inv V' V hle, ?_, ?_⟩, ?_⟩
  · rw [← cancel_mono V'.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [← cancel_mono V.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  · exact Scheme.Hom.resLE_comp_ι ..
private theorem ker_eq_of_iso_comp {P Q T : Scheme.{u}} (c : Q ≅ P) (h₁ : P ⟶ T) (h₂ : Q ⟶ T)
    (hc : c.hom ≫ h₁ = h₂) : h₁.ker = h₂.ker := by
  rw [← hc, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]
namespace IsPushforwardBlowupSeq
end IsPushforwardBlowupSeq
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X X₁ Y Y₁ : Scheme.{u}}
    (φ : X₁ ⟶ X) (ψ : Y₁ ⟶ Y) (u : X ⟶ Y) (u₁ : X₁ ⟶ Y₁) [IsIso u] [IsIso u₁]
    (hsq : u₁ ≫ ψ = φ ≫ u) (Z D : X.IdealSheafData) :
    imageIdealSheaf u₁ (Blowup.strictTransform φ Z D)
      = Blowup.strictTransform ψ (imageIdealSheaf u Z) (imageIdealSheaf u D) := by
  have hψ : ψ = inv u₁ ≫ φ ≫ u := by
    rw [← hsq, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hmaps : ψ ≫ inv u = inv u₁ ≫ φ := by
    rw [hψ, Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hcm : ∀ I : X.IdealSheafData,
      (imageIdealSheaf u I).comap ψ = (I.comap φ).comap (inv u₁) := by
    intro I
    rw [imageIdealSheaf_eq_comap_inv,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hmaps]
  obtain ⟨θ, hθ⟩ := exists_iso_subscheme_comap_of_isIso (inv u₁) (D.comap φ)
  have hVV' : (TopologicalSpace.Opens.map ((D.comap φ).comap (inv u₁)).subschemeι.base).obj
        ((Z.comap φ).comap (inv u₁)).support.compl
      = (TopologicalSpace.Opens.map θ.hom.base).obj
        ((TopologicalSpace.Opens.map (D.comap φ).subschemeι.base).obj
          (Z.comap φ).support.compl) := by
    rw [compl_support_comap, ← opens_map_comp, ← opens_map_comp, hθ]
  obtain ⟨c, hc⟩ := exists_iso_opens_preimage θ _ _ hVV'
  rw [Blowup.strictTransform_eq_ker, Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq,
    Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq, Blowup.strictTransformOpens_eq,
    hcm Z, hcm D, ← ker_comp_eq_imageIdealSheaf_ker]
  refine ker_eq_of_iso_comp c _ _ ?_
  simp only [Category.assoc]
  rw [← Category.assoc c.hom, hc, Category.assoc, reassoc_of% hθ]
  simp
end FunctorialResolution.EmbeddedResolution
