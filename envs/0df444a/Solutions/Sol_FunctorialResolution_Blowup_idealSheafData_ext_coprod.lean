-- Prove2me | solution 1 for FunctorialResolution.Blowup.idealSheafData_ext_coprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:22:57.650463+00:00
-- url     : https://prove2.me/submissions/3169471c-8d7c-4710-a136-b6e2c54b5649

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
namespace FunctorialResolution.Blowup
private theorem preimage_image_opens {W Z : Scheme.{u}} (g : W ⟶ Z) [IsOpenImmersion g]
    (V : W.Opens) : g ⁻¹ᵁ (g ''ᵁ V) = V := by
  refine TopologicalSpace.Opens.ext ?_
  show ⇑g.base ⁻¹' (⇑g.base '' (V : Set ↥W)) = (V : Set ↥W)
  exact Set.preimage_image_eq _ g.isOpenEmbedding.injective
private theorem ideal_eq_of_map_eq_of_bijective {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Bijective φ) {K L : Ideal A}
    (h : Ideal.map φ K = Ideal.map φ L) : K = L := by
  have key : ∀ K' L' : Ideal A, Ideal.map φ K' = Ideal.map φ L' → K' ≤ L' := by
    intro K' L' h' x hx
    have hx' : φ x ∈ Ideal.map φ L' := by
      rw [← h']
      exact Ideal.mem_map_of_mem φ hx
    obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective φ hφ.2).mp hx'
    rwa [← hφ.1 hxy]
  exact le_antisymm (key K L h) (key L K h.symm)
private theorem bijective_of_isIso {A B : CommRingCat.{u}} (φ : A ⟶ B) [IsIso φ] :
    Function.Bijective (CommRingCat.Hom.hom φ) := by
  have h3 : ∀ c : A, CommRingCat.Hom.hom (inv φ) (CommRingCat.Hom.hom φ c) = c := fun c =>
    congrArg (fun ψ : A ⟶ A => CommRingCat.Hom.hom ψ c) (IsIso.hom_inv_id φ)
  constructor
  · intro a a' h
    have h2 : CommRingCat.Hom.hom (inv φ) (CommRingCat.Hom.hom φ a)
        = CommRingCat.Hom.hom (inv φ) (CommRingCat.Hom.hom φ a') := by rw [h]
    simp only [h3] at h2
    exact h2
  · intro b
    exact ⟨CommRingCat.Hom.hom (inv φ) b,
      congrArg (fun ψ : B ⟶ B => CommRingCat.Hom.hom ψ b) (IsIso.inv_hom_id φ)⟩
private theorem appLE_image_bijective_of_isOpenImmersion {W Z : Scheme.{u}} (g : W ⟶ Z)
    [IsOpenImmersion g] (V : W.Opens) (e : V ≤ g ⁻¹ᵁ (g ''ᵁ V)) :
    Function.Bijective (CommRingCat.Hom.hom (g.appLE (g ''ᵁ V) V e)) := by
  have hpre : g ⁻¹ᵁ (g ''ᵁ V) = V := preimage_image_opens g V
  have : IsIso (homOfLE e) := ⟨homOfLE hpre.le, rfl, rfl⟩
  have : IsIso (g.appLE (g ''ᵁ V) V e) := by
    show IsIso (g.app (g ''ᵁ V) ≫ W.presheaf.map (homOfLE e).op)
    infer_instance
  exact bijective_of_isIso (g.appLE (g ''ᵁ V) V e)
private theorem ideal_image_eq_of_comap_eq {W Z : Scheme.{u}} (g : W ⟶ Z) [IsOpenImmersion g]
    {I J : Z.IdealSheafData} (h : I.comap g = J.comap g) (V : ↥(W.affineOpens)) :
    I.ideal ⟨g ''ᵁ (V : W.Opens), isAffineOpen_image g (V : W.Opens) V.2⟩
      = J.ideal ⟨g ''ᵁ (V : W.Opens), isAffineOpen_image g (V : W.Opens) V.2⟩ := by
  have e : (V : W.Opens) ≤ g ⁻¹ᵁ (g ''ᵁ (V : W.Opens)) :=
    (preimage_image_opens g (V : W.Opens)).ge
  have h1 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE I g
    ⟨g ''ᵁ (V : W.Opens), isAffineOpen_image g (V : W.Opens) V.2⟩ V e
  have h2 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE J g
    ⟨g ''ᵁ (V : W.Opens), isAffineOpen_image g (V : W.Opens) V.2⟩ V e
  have h3 : (I.comap g).ideal V = (J.comap g).ideal V := by rw [h]
  rw [h1, h2] at h3
  exact ideal_eq_of_map_eq_of_bijective _ (appLE_image_bijective_of_isOpenImmersion g (V : W.Opens) e) h3
private theorem exists_affineOpen_mem (X : Scheme.{u}) (x : ↥X) :
    ∃ V : ↥(X.affineOpens), x ∈ ((V : X.Opens) : Set ↥X) := by
  have h : x ∈ (⨆ V : ↥(X.affineOpens), (V : X.Opens)) := by
    rw [iSup_affineOpens_eq_top X]
    exact trivial
  obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp h
  exact ⟨V, SetLike.mem_coe.mpr hV⟩
end FunctorialResolution.Blowup
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
theorem _root_.solution {X Y : Scheme.{u}} (I J : (X ⨿ Y).IdealSheafData)
    (hl : I.comap (coprod.inl : X ⟶ X ⨿ Y) = J.comap (coprod.inl : X ⟶ X ⨿ Y))
    (hr : I.comap (coprod.inr : Y ⟶ X ⨿ Y) = J.comap (coprod.inr : Y ⟶ X ⨿ Y)) :
    I = J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (Sum.elim
      (fun V : ↥(X.affineOpens) =>
        (⟨(coprod.inl : X ⟶ X ⨿ Y) ''ᵁ (V : X.Opens),
          isAffineOpen_image (coprod.inl : X ⟶ X ⨿ Y) (V : X.Opens) V.2⟩ :
            ↥((X ⨿ Y).affineOpens)))
      (fun V : ↥(Y.affineOpens) =>
        (⟨(coprod.inr : Y ⟶ X ⨿ Y) ''ᵁ (V : Y.Opens),
          isAffineOpen_image (coprod.inr : Y ⟶ X ⨿ Y) (V : Y.Opens) V.2⟩ :
            ↥((X ⨿ Y).affineOpens)))) ?_ ?_
  · rw [eq_top_iff]
    intro z _
    by_cases hz : z ∈ Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base
    · obtain ⟨x, rfl⟩ := hz
      obtain ⟨V, hV⟩ := exists_affineOpen_mem X x
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨Sum.inl V, ?_⟩
      exact SetLike.mem_coe.mp (Set.mem_image_of_mem _ hV)
    · have hz' : z ∈ Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base := by
        rw [range_coprod_inr_eq_compl X Y]
        exact hz
      obtain ⟨y, rfl⟩ := hz'
      obtain ⟨V, hV⟩ := exists_affineOpen_mem Y y
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨Sum.inr V, ?_⟩
      exact SetLike.mem_coe.mp (Set.mem_image_of_mem _ hV)
  · rintro (V | V)
    · exact ideal_image_eq_of_comap_eq (coprod.inl : X ⟶ X ⨿ Y) hl V
    · exact ideal_image_eq_of_comap_eq (coprod.inr : Y ⟶ X ⨿ Y) hr V
end FunctorialResolution.Blowup
