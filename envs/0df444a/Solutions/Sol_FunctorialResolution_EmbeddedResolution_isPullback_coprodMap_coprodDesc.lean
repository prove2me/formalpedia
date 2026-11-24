-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isPullback_coprodMap_coprodDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:01:28.529519+00:00
-- url     : https://prove2.me/submissions/af35abdf-4a61-4594-842c-20494621e840

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_CoproductBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_BinaryCoproductBaseChange
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_sigmaMap_sigmaDesc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FunctorialResolution.EmbeddedResolution
private theorem pairInl_comp_map {X₁ X₂ P₁ P₂ : Scheme.{u}} (a₁ : P₁ ⟶ X₁) (a₂ : P₂ ⟶ X₂) :
    sigmaBoolFamilyInl P₁ P₂ ≫ Limits.Sigma.map (boolFamilyMap a₁ a₂) = a₁ ≫ sigmaBoolFamilyInl X₁ X₂ :=
  Limits.Sigma.ι_map (boolFamilyMap a₁ a₂) ⟨true⟩
private theorem pairInr_comp_map {X₁ X₂ P₁ P₂ : Scheme.{u}} (a₁ : P₁ ⟶ X₁) (a₂ : P₂ ⟶ X₂) :
    sigmaBoolFamilyInr P₁ P₂ ≫ Limits.Sigma.map (boolFamilyMap a₁ a₂) = a₂ ≫ sigmaBoolFamilyInr X₁ X₂ :=
  Limits.Sigma.ι_map (boolFamilyMap a₁ a₂) ⟨false⟩
private theorem pairCoprodIso_hom (X₁ X₂ : Scheme.{u}) :
    (coprodIsoSigmaBoolFamily X₁ X₂).hom = coprod.desc (sigmaBoolFamilyInl X₁ X₂) (sigmaBoolFamilyInr X₁ X₂) := rfl
private theorem isPullback_of_isPullback_of_iso {P X Y Z P' X' : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {fst' : P' ⟶ X'} {snd' : P' ⟶ Y} {f' : X' ⟶ Z}
    (h : IsPullback fst snd f g) (eP : P' ≅ P) (eX : X' ≅ X)
    (h1 : fst' ≫ eX.hom = eP.hom ≫ fst) (h2 : eX.hom ≫ f = f')
    (h3 : eP.hom ≫ snd = snd') : IsPullback fst' snd' f' g := by
  have sq2 : CommSq eX.inv f f' (𝟙 Z) := by
    refine ⟨?_⟩
    rw [← h2, Iso.inv_hom_id_assoc, Category.comp_id]
  have hX : IsPullback eX.inv f f' (𝟙 Z) := IsPullback.of_horiz_isIso sq2
  have step1 := h.paste_horiz hX
  have sq1 : CommSq eP.hom (eP.hom ≫ snd) snd (𝟙 Y) := by
    refine ⟨?_⟩
    rw [Category.comp_id]
  have hP : IsPullback eP.hom (eP.hom ≫ snd) snd (𝟙 Y) := IsPullback.of_horiz_isIso sq1
  have step2 := hP.paste_horiz step1
  have hfst : fst' = eP.hom ≫ fst ≫ eX.inv := by
    rw [← Category.assoc, ← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hfst, ← h3]
  simpa using step2
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X₁ X₂ P₁ P₂ Y Y' : Scheme.{u}}
    (a₁ : P₁ ⟶ X₁) (a₂ : P₂ ⟶ X₂) (b₁ : P₁ ⟶ Y') (b₂ : P₂ ⟶ Y')
    (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) (u : Y' ⟶ Y)
    (h₁ : IsPullback a₁ b₁ f₁ u) (h₂ : IsPullback a₂ b₂ f₂ u) :
    IsPullback (coprod.map a₁ a₂) (coprod.desc b₁ b₂) (coprod.desc f₁ f₂) u := by
  have hsq : ∀ i : ULift.{u} Bool,
      IsPullback (boolFamilyMap a₁ a₂ i) (boolFamilyDesc b₁ b₂ i) (boolFamilyDesc f₁ f₂ i) u := by
    rintro ⟨(_ | _)⟩
    · exact h₂
    · exact h₁
  have key := isPullback_sigmaMap_sigmaDesc u (boolFamily X₁ X₂) (boolFamily P₁ P₂)
      (boolFamilyMap a₁ a₂) (boolFamilyDesc b₁ b₂) (boolFamilyDesc f₁ f₂) hsq
  have E1 : coprod.map a₁ a₂ ≫ (coprodIsoSigmaBoolFamily X₁ X₂).hom
      = (coprodIsoSigmaBoolFamily P₁ P₂).hom ≫ Limits.Sigma.map (boolFamilyMap a₁ a₂) := by
    simp only [pairCoprodIso_hom]
    apply coprod.hom_ext
    · rw [coprod.inl_map_assoc, coprod.inl_desc, coprod.inl_desc_assoc, pairInl_comp_map]
    · rw [coprod.inr_map_assoc, coprod.inr_desc, coprod.inr_desc_assoc, pairInr_comp_map]
  have E2 : (coprodIsoSigmaBoolFamily X₁ X₂).hom ≫ Limits.Sigma.desc (boolFamilyDesc f₁ f₂)
      = coprod.desc f₁ f₂ := by
    simp only [pairCoprodIso_hom]
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, pairInl_comp_desc, coprod.inl_desc]
    · rw [coprod.inr_desc_assoc, pairInr_comp_desc, coprod.inr_desc]
  have E3 : (coprodIsoSigmaBoolFamily P₁ P₂).hom ≫ Limits.Sigma.desc (boolFamilyDesc b₁ b₂)
      = coprod.desc b₁ b₂ := by
    simp only [pairCoprodIso_hom]
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, pairInl_comp_desc, coprod.inl_desc]
    · rw [coprod.inr_desc_assoc, pairInr_comp_desc, coprod.inr_desc]
  exact isPullback_of_isPullback_of_iso key (coprodIsoSigmaBoolFamily P₁ P₂) (coprodIsoSigmaBoolFamily X₁ X₂) E1 E2 E3
end FunctorialResolution.EmbeddedResolution
