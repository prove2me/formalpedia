-- Prove2me | solution 1 for FunctorialResolution.Blowup.ker_comp_coprod_inl_comap_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:17.209797+00:00
-- url     : https://prove2.me/submissions/88a98d66-58ed-475a-8519-2e7374c31967

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
private theorem map_ker_comp_of_surjective {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (hφ : Function.Surjective φ) :
    Ideal.map φ (RingHom.ker (ψ.comp φ)) = RingHom.ker ψ := by
  rw [RingHom.ker_eq_comap_bot (ψ.comp φ), ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot]
  exact Ideal.map_comap_of_surjective φ hφ _
private theorem surjective_of_isIso {A B : CommRingCat.{u}} (φ : A ⟶ B) (hφ : IsIso φ) :
    Function.Surjective (CommRingCat.Hom.hom φ) := by
  have := hφ
  intro y
  exact ⟨CommRingCat.Hom.hom (inv φ) y,
    congrArg (fun ψ : B ⟶ B => CommRingCat.Hom.hom ψ y) (IsIso.inv_hom_id φ)⟩
private theorem preimage_image_opens {W Z : Scheme.{u}} (g : W ⟶ Z) [IsOpenImmersion g]
    (V : W.Opens) : g ⁻¹ᵁ (g ''ᵁ V) = V := by
  refine TopologicalSpace.Opens.ext ?_
  show ⇑g.base ⁻¹' (⇑g.base '' (V : Set ↥W)) = (V : Set ↥W)
  exact Set.preimage_image_eq _ g.isOpenEmbedding.injective
private theorem ker_ideal_eq_ker_app {T W : Scheme.{u}} (f : T ⟶ W) [QuasiCompact f]
    (U : W.affineOpens) :
    f.ker.ideal U = RingHom.ker (CommRingCat.Hom.hom (f.app (U : W.Opens))) := by
  simp
private theorem map_appLE_ker_comp {T W Z : Scheme.{u}} (f : T ⟶ W) (g : W ⟶ Z)
    (U : Z.Opens) (V : W.Opens) (hUV : g ⁻¹ᵁ U = V) (e : V ≤ g ⁻¹ᵁ U)
    (hsurj : Function.Surjective (CommRingCat.Hom.hom (g.app U))) :
    Ideal.map (CommRingCat.Hom.hom (g.appLE U V e))
        (RingHom.ker (CommRingCat.Hom.hom ((f ≫ g).app U)))
      = RingHom.ker (CommRingCat.Hom.hom (f.app V)) := by
  subst hUV
  have hid : g.appLE U (g ⁻¹ᵁ U) e = g.app U := by
    show g.app U ≫ W.presheaf.map (homOfLE e).op = g.app U
    have h1 : (homOfLE e).op = 𝟙 (Opposite.op (g ⁻¹ᵁ U)) := rfl
    rw [h1, W.presheaf.map_id, Category.comp_id]
  have hcomp : CommRingCat.Hom.hom ((f ≫ g).app U)
      = RingHom.comp (CommRingCat.Hom.hom (f.app (g ⁻¹ᵁ U)))
          (CommRingCat.Hom.hom (g.app U)) := rfl
  rw [hid, hcomp]
  exact map_ker_comp_of_surjective _ _ hsurj
private theorem ker_comap_of_isOpenImmersion {T W Z : Scheme.{u}} (f : T ⟶ W) (g : W ⟶ Z)
    [IsOpenImmersion g] [QuasiCompact f] [QuasiCompact (f ≫ g)] :
    (f ≫ g).ker.comap g = f.ker := by
  have key : ∀ V : W.affineOpens, ((f ≫ g).ker.comap g).ideal V = f.ker.ideal V := by
    intro V
    have hU : IsAffineOpen (g ''ᵁ (V : W.Opens)) := isAffineOpen_image g (V : W.Opens) V.2
    have hpre : g ⁻¹ᵁ (g ''ᵁ (V : W.Opens)) = (V : W.Opens) :=
      preimage_image_opens g (V : W.Opens)
    have e : (V : W.Opens) ≤ g ⁻¹ᵁ (g ''ᵁ (V : W.Opens)) := hpre.ge
    have h1 : ((f ≫ g).ker.comap g).ideal V
        = Ideal.map (CommRingCat.Hom.hom (g.appLE (g ''ᵁ (V : W.Opens)) (V : W.Opens) e))
            ((f ≫ g).ker.ideal ⟨g ''ᵁ (V : W.Opens), hU⟩) :=
      Scheme.IdealSheafData.comap_ideal_eq_map_appLE ((f ≫ g).ker) g
        ⟨g ''ᵁ (V : W.Opens), hU⟩ V e
    rw [h1, ker_ideal_eq_ker_app (f ≫ g) ⟨g ''ᵁ (V : W.Opens), hU⟩, ker_ideal_eq_ker_app f V]
    exact map_appLE_ker_comp f g (g ''ᵁ (V : W.Opens)) (V : W.Opens) hpre e
      (surjective_of_isIso (g.app (g ''ᵁ (V : W.Opens))) inferInstance)
  ext V
  rw [key V]
end FunctorialResolution.Blowup
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
theorem _root_.solution {X Y Z : Scheme.{u}} (f : Z ⟶ X)
    [QuasiCompact f] [QuasiCompact (f ≫ (coprod.inl : X ⟶ X ⨿ Y))] :
    (f ≫ (coprod.inl : X ⟶ X ⨿ Y)).ker.comap (coprod.inl : X ⟶ X ⨿ Y) = f.ker :=
  ker_comap_of_isOpenImmersion f (coprod.inl : X ⟶ X ⨿ Y)
end FunctorialResolution.Blowup
