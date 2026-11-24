-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isStrictNormalCrossingsAt_base_of_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:49.685861+00:00
-- url     : https://prove2.me/submissions/83b83e6f-b32d-4565-acd4-cf6dccb42119

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsOpenImmersion
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem ideal_eq_span_of_map_eq_span {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (ψ : S →+* R) (hψφ : ∀ r, ψ (φ r) = r) (I : Ideal R) (b : S)
    (hb : Ideal.map φ I = Ideal.span {b}) : I = Ideal.span {ψ b} := by
  have h2 : Ideal.map ψ (Ideal.map φ I) = I := by
    rw [Ideal.map_map, show ψ.comp φ = RingHom.id R from RingHom.ext hψφ, Ideal.map_id]
  rw [← h2, hb, Ideal.map_span, Set.image_singleton]
private theorem isRegularParameterSystem_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (v : Fin n → R) (w : Fin n → S)
    (hvw : ∀ i, e (v i) = w i) (hv : IsRegularParameterSystem R n v) :
    IsRegularParameterSystem S n w := by
  have h1 := hv.1
  have h2 := hv.2
  refine ⟨?_, ?_⟩
  · have hw : w = fun i => (e : R →+* S) (v i) := funext fun i => (hvw i).symm
    rw [hw, show (Set.range fun i => (e : R →+* S) (v i)) = (e : R →+* S) '' Set.range v from
      Set.range_comp _ _, ← Ideal.map_span, h1]
    exact IsLocalRing.map_ringEquiv_maximalIdeal e
  · rw [h2]
    exact ringKrullDim_eq_of_ringEquiv e
private theorem isIso_appLE_image {X Y : Scheme.{u}} (h : X ⟶ Y) [IsOpenImmersion h] (U : X.Opens)
    (e : U ≤ (TopologicalSpace.Opens.map h.base).obj (h ''ᵁ U)) :
    IsIso (h.appLE (h ''ᵁ U) U e) := by
  rw [show h.appLE (h ''ᵁ U) U e = (h.appIso U).hom from (Scheme.Hom.appIso_hom' h U).symm]
  infer_instance
private theorem stalkMap_germ_eq_germ_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ (TopologicalSpace.Opens.map f.base).obj U) (x : X) (hx : x ∈ V)
    (hfx : f.base x ∈ U) (s : Γ(Y, U)) :
    f.stalkMap x (Y.presheaf.germ U (f.base x) hfx s)
      = X.presheaf.germ V x hx (f.appLE U V e s) := by
  have key : Y.presheaf.germ U (f.base x) hfx ≫ f.stalkMap x
      = f.app U ≫ X.presheaf.germ ((TopologicalSpace.Opens.map f.base).obj U) x hfx := by
    simp
  have key2 : f.stalkMap x (Y.presheaf.germ U (f.base x) hfx s)
      = X.presheaf.germ ((TopologicalSpace.Opens.map f.base).obj U) x hfx (f.app U s) := by
    rw [← CommRingCat.comp_apply, key, CommRingCat.comp_apply]
  have h1 : f.appLE U V e s = X.presheaf.map (homOfLE e).op (f.app U s) := rfl
  rw [key2, h1, TopCat.Presheaf.germ_res_apply]
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X' Y' : Scheme.{u}} (h : X' ⟶ Y') [IsOpenImmersion h]
    (E : Y'.IdealSheafData) (hE : IsStrictNormalCrossingsDivisor (E.comap h)) (x : X') :
    IsRegularLocalRing (Y'.presheaf.stalk (h.base x)) ∧
      ∃ (U : Y'.affineOpens) (hy : h.base x ∈ U.1) (n : ℕ) (f : Fin n → Γ(Y', U.1))
        (J : Finset (Fin n)),
        IsRegularParameterSystem (Y'.presheaf.stalk (h.base x)) n
            (fun i => Y'.presheaf.germ U.1 (h.base x) hy (f i)) ∧
          E.ideal U = Ideal.span {∏ i ∈ J, f i} := by
  obtain ⟨hreg, U', hx, n, g, J, hparams, hideal⟩ := hE x
  have : IsRegularLocalRing (X'.presheaf.stalk x) := hreg
  have hU : IsAffineOpen (h ''ᵁ U'.1) := U'.2.image_of_isOpenImmersion h
  have he : U'.1 ≤ (TopologicalSpace.Opens.map h.base).obj (h ''ᵁ U'.1) :=
    le_of_eq (Scheme.Hom.preimage_image_eq h U'.1).symm
  have hy : h.base x ∈ h ''ᵁ U'.1 := ⟨x, hx, rfl⟩
  have : IsIso (h.appLE (h ''ᵁ U'.1) U'.1 he) := isIso_appLE_image h U'.1 he
  have : IsIso (h.stalkMap x) := inferInstance
  let ε : Γ(Y', h ''ᵁ U'.1) ≃+* Γ(X', U'.1) :=
    (asIso (h.appLE (h ''ᵁ U'.1) U'.1 he)).commRingCatIsoToRingEquiv
  let τ : Y'.presheaf.stalk (h.base x) ≃+* X'.presheaf.stalk x :=
    (asIso (h.stalkMap x)).commRingCatIsoToRingEquiv
  have hgerm : ∀ i, τ (Y'.presheaf.germ (h ''ᵁ U'.1) (h.base x) hy (ε.symm (g i)))
      = X'.presheaf.germ U'.1 x hx (g i) := by
    intro i
    have h1 := stalkMap_germ_eq_germ_appLE h (h ''ᵁ U'.1) U'.1 he x hx hy (ε.symm (g i))
    have h2 : (h.appLE (h ''ᵁ U'.1) U'.1 he) (ε.symm (g i)) = g i := ε.apply_symm_apply (g i)
    rw [h2] at h1
    exact h1
  refine ⟨IsRegularLocalRing.of_ringEquiv τ.symm, ⟨h ''ᵁ U'.1, hU⟩, hy, n,
    fun i => ε.symm (g i), J, ?_, ?_⟩
  · refine isRegularParameterSystem_of_ringEquiv τ.symm n
      (fun i => X'.presheaf.germ U'.1 x hx (g i))
      (fun i => Y'.presheaf.germ (h ''ᵁ U'.1) (h.base x) hy (ε.symm (g i))) ?_ hparams
    intro i
    rw [← hgerm i, τ.symm_apply_apply]
  · have hmap := Scheme.IdealSheafData.comap_ideal_eq_map_appLE E h ⟨h ''ᵁ U'.1, hU⟩ U' he
    rw [hideal] at hmap
    have hprod : (ε.symm : Γ(X', U'.1) →+* Γ(Y', h ''ᵁ U'.1)) (∏ i ∈ J, g i)
        = ∏ i ∈ J, ε.symm (g i) := map_prod _ _ _
    rw [ideal_eq_span_of_map_eq_span ((h.appLE (h ''ᵁ U'.1) U'.1 he).hom)
      (ε.symm : Γ(X', U'.1) →+* Γ(Y', h ''ᵁ U'.1)) (fun r => ε.symm_apply_apply r)
      (E.ideal ⟨h ''ᵁ U'.1, hU⟩) (∏ i ∈ J, g i) hmap.symm, hprod]
end FunctorialResolution.EmbeddedResolution
