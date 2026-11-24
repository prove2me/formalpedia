-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_eq_prod_of_isMonomialOnOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:28:25.829488+00:00
-- url     : https://prove2.me/submissions/85b4c859-e48e-44cd-87b7-12606aedaf8c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtMultiplicativity
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialPartAlongDivisor
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplitting
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplittingUniqueness
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_comap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_listProd
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_pow
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap___a4ce28546e44

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}}
private theorem ideal_map_listProd {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (L : List (Ideal R)) :
    Ideal.map f L.prod = (L.map (fun I => Ideal.map f I)).prod :=
  map_list_prod (Ideal.mapHom f) L
private theorem eq_of_ideal_map_eq_of_ringHom_leftInverse {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : S →+* R) (hgf : ∀ z, g (f z) = z) {A B : Ideal R}
    (hAB : Ideal.map f A = Ideal.map f B) : A = B := by
  have hcomp : g.comp f = RingHom.id R := RingHom.ext hgf
  have hA : Ideal.map g (Ideal.map f A) = A := by rw [Ideal.map_map, hcomp, Ideal.map_id]
  have hB : Ideal.map g (Ideal.map f B) = B := by rw [Ideal.map_map, hcomp, Ideal.map_id]
  rw [← hA, ← hB, hAB]
private theorem hom_apply_hom_apply_of_comp_eq {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (k : A ⟶ C) (hk : f ≫ g = k) (z : A) : g.hom (f.hom z) = k.hom z := by
  rw [← hk, CommRingCat.hom_comp]
  rfl
private theorem inv_hom_apply_hom_apply {A B : CommRingCat.{u}} (f : A ⟶ B) [IsIso f]
    (z : A) : (inv f).hom (f.hom z) = z := by
  rw [hom_apply_hom_apply_of_comp_eq f (inv f) (𝟙 A) (IsIso.hom_inv_id f) z, CommRingCat.hom_id]
  rfl
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (E : List X.IdealSheafData) (M : X.IdealSheafData)
    (U : X.Opens) (a : Fin E.length → ℕ) (h : IsMonomialOnOpen E M U a) (x : X) (hx : x ∈ U) :
    stalkIdeal M x =
      ((List.finRange E.length).map (fun j => stalkIdeal (E.get j) x ^ a j)).prod := by
  have h' : restrictIdeal M U
      = ((List.finRange E.length).map (fun j => restrictIdeal (E.get j) U ^ a j)).prod := h
  have hxr : x ∈ Set.range (⇑U.ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact hx
  obtain ⟨y, hy⟩ := hxr
  subst hy
  have hgf : ∀ z, (inv (U.ι.stalkMap y)).hom ((U.ι.stalkMap y).hom z) = z :=
    fun z => inv_hom_apply_hom_apply (U.ι.stalkMap y) z
  refine eq_of_ideal_map_eq_of_ringHom_leftInverse (U.ι.stalkMap y).hom (inv (U.ι.stalkMap y)).hom hgf ?_
  have hL : ((List.finRange E.length).map
        (fun j => stalkIdeal (E.get j) (U.ι.base y) ^ a j)).map
        (fun I => Ideal.map (U.ι.stalkMap y).hom I)
      = ((List.finRange E.length).map (fun j => restrictIdeal (E.get j) U ^ a j)).map
        (fun I => stalkIdeal I y) := by
    rw [List.map_map, List.map_map]
    refine List.map_congr_left ?_
    intro j _
    show Ideal.map (U.ι.stalkMap y).hom (stalkIdeal (E.get j) (U.ι.base y) ^ a j)
        = stalkIdeal (restrictIdeal (E.get j) U ^ a j) y
    rw [stalkIdeal_pow, restrictIdeal_eq_comap_ι, stalkIdeal_comap, Ideal.map_pow]
  rw [ideal_map_listProd, hL, ← stalkIdeal_listProd, ← h', restrictIdeal_eq_comap_ι,
    stalkIdeal_comap]
end FunctorialResolution.EmbeddedResolution
