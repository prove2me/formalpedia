-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:58.921063+00:00
-- url     : https://prove2.me/submissions/9a97820a-de67-4133-a098-406f308b582d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_map_germ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_idealOrder
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineOpens_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_le_idealOrder_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
private theorem map_maximalIdeal_of_inverse {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) (g : S →+* R)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ x, f (g x) = x) :
    Ideal.map f (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hx
    have h2 := hu.map g
    rwa [hgf] at h2
  · intro z hz
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz
    have hgz : g z ∈ IsLocalRing.maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply hz
      have h2 := hu.map f
      rwa [hfg] at h2
    have h3 : f (g z) ∈ Ideal.map f (IsLocalRing.maximalIdeal R) := Ideal.mem_map_of_mem _ hgz
    rwa [hfg] at h3
private theorem idealOrder_map_of_inverse {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) (g : S →+* R)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ x, f (g x) = x) (J : Ideal R) :
    idealOrder (Ideal.map f J) = idealOrder J := by
  have hf := map_maximalIdeal_of_inverse f g hgf hfg
  have hg := map_maximalIdeal_of_inverse g f hfg hgf
  have h1 : idealOrder J ≤ idealOrder (Ideal.map f J) :=
    idealOrder_le_idealOrder_map f hf.le J
  have hcomp : g.comp f = RingHom.id R := RingHom.ext hgf
  have h2 : Ideal.map g (Ideal.map f J) = J := by
    rw [Ideal.map_map, hcomp, Ideal.map_id]
  have h3 : idealOrder (Ideal.map f J) ≤ idealOrder (Ideal.map g (Ideal.map f J)) :=
    idealOrder_le_idealOrder_map g hg.le (Ideal.map f J)
  rw [h2] at h3
  exact le_antisymm h3 h1
open CategoryTheory in
private theorem hom_hom_apply_of_comp_eq {A B C : CommRingCat} (f : A ⟶ B) (g : B ⟶ C)
    (k : A ⟶ C) (hk : f ≫ g = k) (x : A) : g.hom (f.hom x) = k.hom x := by
  rw [← hk, CommRingCat.hom_comp]
  rfl
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
open CategoryTheory
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {Y : Scheme.{u}} (h : Y ⟶ X) [IsOpenImmersion h]
    (I : X.IdealSheafData) (y : Y) :
    orderAt (I.comap h) y = orderAt I (h.base y) := by
  obtain ⟨U, sectionFrameQuotient⟩ := Y.exists_affineOpens_mem y
  have hyU : y ∈ U.1 := sectionFrameQuotient
  have hVaff : IsAffineOpen (h ''ᵁ U.1) := U.2.image_of_isOpenImmersion h
  have hxV : h.base y ∈ (h ''ᵁ U.1) := ⟨y, hyU, rfl⟩
  let appEquiv : Γ(X, h ''ᵁ U.1) ≃+* Γ(Y, U.1) := (h.appIso U.1).commRingCatIsoToRingEquiv
  have hid : (I.comap h).ideal U
      = Ideal.map ((h.appIso U.1).hom).hom (I.ideal ⟨h ''ᵁ U.1, hVaff⟩) := by
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I h U]
    exact Ideal.comap_symm appEquiv ..
  have key : (h.appIso U.1).inv ≫
        (h.app (h ''ᵁ U.1) ≫ Y.presheaf.germ (h ⁻¹ᵁ h ''ᵁ U.1) y hxV)
      = Y.presheaf.germ U.1 y hyU := by
    rw [← Category.assoc, Scheme.Hom.appIso_inv_app]
    exact Y.presheaf.germ_res _ y hxV
  have hcat : (h.appIso U.1).hom ≫ Y.presheaf.germ U.1 y hyU
      = X.presheaf.germ (h ''ᵁ U.1) (h.base y) hxV ≫ h.stalkMap y := by
    calc (h.appIso U.1).hom ≫ Y.presheaf.germ U.1 y hyU
        = (h.appIso U.1).hom ≫ ((h.appIso U.1).inv ≫
            (h.app (h ''ᵁ U.1) ≫ Y.presheaf.germ (h ⁻¹ᵁ h ''ᵁ U.1) y hxV)) := by rw [key]
      _ = h.app (h ''ᵁ U.1) ≫ Y.presheaf.germ (h ⁻¹ᵁ h ''ᵁ U.1) y hxV := by
          rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      _ = X.presheaf.germ (h ''ᵁ U.1) (h.base y) hxV ≫ h.stalkMap y :=
          (Scheme.Hom.germ_stalkMap h (h ''ᵁ U.1) y hxV).symm
  have hcomp : (Y.presheaf.germ U.1 y hyU).hom.comp ((h.appIso U.1).hom).hom
      = ((h.stalkMap y).hom).comp (X.presheaf.germ (h ''ᵁ U.1) (h.base y) hxV).hom := by
    have h4 := congrArg CommRingCat.Hom.hom hcat
    rwa [CommRingCat.hom_comp, CommRingCat.hom_comp] at h4
  have hsgf : ∀ x, ((inv (h.stalkMap y)).hom) ((h.stalkMap y).hom x) = x := fun x => by
    rw [hom_hom_apply_of_comp_eq _ _ _ (IsIso.hom_inv_id (h.stalkMap y)) x, CommRingCat.hom_id]
    rfl
  have hsfg : ∀ x, ((h.stalkMap y).hom) ((inv (h.stalkMap y)).hom x) = x := fun x => by
    rw [hom_hom_apply_of_comp_eq _ _ _ (IsIso.inv_hom_id (h.stalkMap y)) x, CommRingCat.hom_id]
    rfl
  rw [orderAt_eq_idealOrder, orderAt_eq_idealOrder,
    stalkIdeal_eq_map_germ (I.comap h) y U hyU,
    stalkIdeal_eq_map_germ I (h.base y) ⟨h ''ᵁ U.1, hVaff⟩ hxV, hid, Ideal.map_map, hcomp,
    ← Ideal.map_map]
  exact idealOrder_map_of_inverse (h.stalkMap y).hom (inv (h.stalkMap y)).hom hsgf hsfg _
end FunctorialResolution.EmbeddedResolution
