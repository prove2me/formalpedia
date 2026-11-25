-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isPullback_comp_inl_coprodDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:24:08.295616+00:00
-- url     : https://prove2.me/submissions/49e1fed3-8dbd-445f-bb61-42fedc07d175

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_CoproductBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_BinaryCoproductBaseChange
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_coprodMap_coprodDesc
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_initial_of_isEmpty
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
private theorem coprodInitialIsoRight_hom (P : Scheme.{u}) :
    (isoCoprodInitial P).hom = (coprod.inl : P ⟶ P ⨿ (⊥_ Scheme.{u})) := rfl
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
theorem _root_.solution {P X Y Y' F : Scheme.{u}}
    (a : P ⟶ X) (b : P ⟶ Y') (q : X ⟶ Y) (u : Y' ⟶ Y) (r : F ⟶ Y)
    (hsq : IsPullback a b q u)
    (hF : ∀ (Q : Scheme.{u}) (c : Q ⟶ F) (d : Q ⟶ Y'), c ≫ r = d ≫ u → IsEmpty Q) :
    IsPullback (a ≫ coprod.inl) b (coprod.desc q r) u := by
  have hFpb : IsPullback (initial.to F) (initial.to Y') r u :=
    isPullback_initial_of_isEmpty r u hF
  have key := isPullback_coprodMap_coprodDesc a (initial.to F) b (initial.to Y') q r u hsq hFpb
  have E1 : (a ≫ coprod.inl) ≫ (Iso.refl (X ⨿ F)).hom
      = (isoCoprodInitial P).hom ≫ coprod.map a (initial.to F) := by
    rw [Iso.refl_hom, Category.comp_id, coprodInitialIsoRight_hom, coprod.inl_map]
  have E2 : (Iso.refl (X ⨿ F)).hom ≫ coprod.desc q r = coprod.desc q r := by
    rw [Iso.refl_hom, Category.id_comp]
  have E3 : (isoCoprodInitial P).hom ≫ coprod.desc b (initial.to Y') = b := by
    rw [coprodInitialIsoRight_hom, coprod.inl_desc]
  exact isPullback_of_isPullback_of_iso key (isoCoprodInitial P) (Iso.refl (X ⨿ F)) E1 E2 E3
end FunctorialResolution.EmbeddedResolution
