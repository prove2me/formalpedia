-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isRegularLocalRing_of_flat_formallyUnramified
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:47.071609+00:00
-- url     : https://prove2.me/submissions/34a4b8b4-ea65-4663-8fa1-b985eb685483

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ringKrullDim_eq_of_flat_formallyUnramified
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
namespace FunctorialResolution.EmbeddedResolution
private theorem spanFinrank_map_le (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing R]
    [Algebra R S] (I : Ideal R) :
    (Ideal.map (algebraMap R S) I).spanFinrank ≤ I.spanFinrank := by
  obtain ⟨s, hcard, hspan⟩ := Submodule.exists_span_set_card_eq_spanRank I
  have hIfg : Submodule.FG (I : Submodule R R) := IsNoetherian.noetherian I
  have hrank : I.spanRank = (I.spanFinrank : Cardinal) :=
    Submodule.FG.spanRank_eq_spanFinrank hIfg
  have hslt : Cardinal.mk s < Cardinal.aleph0 := by
    rw [hcard, hrank]
    exact Cardinal.natCast_lt_aleph0
  have hspan' : Ideal.span s = I := hspan
  have hmapspan : Ideal.map (algebraMap R S) I = Ideal.span ((algebraMap R S) '' s) := by
    rw [← hspan', Ideal.map_span]
  have h1 : (Ideal.map (algebraMap R S) I).spanRank ≤ Cardinal.mk ((algebraMap R S) '' s) := by
    rw [hmapspan]
    exact Submodule.spanRank_span_le_card _
  have h2 := Cardinal.mk_image_le_lift (f := (algebraMap R S : R → S)) (s := s)
  have hliftlt : Cardinal.lift.{_, _} (Cardinal.mk s) < Cardinal.aleph0 :=
    Cardinal.lift_lt_aleph0.mpr hslt
  have h4 : Cardinal.mk ((algebraMap R S) '' s) < Cardinal.aleph0 :=
    Cardinal.lift_lt_aleph0.mp (lt_of_le_of_lt h2 hliftlt)
  have h3 : Cardinal.toNat (Cardinal.mk ((algebraMap R S) '' s)) ≤
      Cardinal.toNat (Cardinal.mk s) := by
    have := Cardinal.toNat_le_toNat h2 hliftlt
    rwa [Cardinal.toNat_lift, Cardinal.toNat_lift] at this
  calc (Ideal.map (algebraMap R S) I).spanFinrank
      = Cardinal.toNat (Ideal.map (algebraMap R S) I).spanRank :=
        Submodule.spanFinrank.eq_def _
    _ ≤ Cardinal.toNat (Cardinal.mk ((algebraMap R S) '' s)) := Cardinal.toNat_le_toNat h1 h4
    _ ≤ Cardinal.toNat (Cardinal.mk s) := h3
    _ = I.spanFinrank := by rw [hcard, ← Submodule.spanFinrank.eq_def]
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [_root_.IsRegularLocalRing R] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    [Module.Flat R S] :
    _root_.IsRegularLocalRing S := by
  have : IsLocalRing R := inferInstance
  have : IsNoetherianRing R := inferInstance
  have hdim : ringKrullDim S = ringKrullDim R := ringKrullDim_eq_of_flat_formallyUnramified R S
  have hR : ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    (isRegularLocalRing_iff R).mp inferInstance
  have hmax : IsLocalRing.maximalIdeal S = (IsLocalRing.maximalIdeal R).map (algebraMap R S) :=
    (Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)).symm
  have h4 : (IsLocalRing.maximalIdeal S).spanFinrank
      ≤ (IsLocalRing.maximalIdeal R).spanFinrank := by
    rw [hmax]
    exact spanFinrank_map_le R S _
  have hh : (IsLocalRing.maximalIdeal S).height
      ≤ ((IsLocalRing.maximalIdeal S).spanFinrank : ℕ∞) :=
    Ideal.height_le_spanFinrank _ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  have hle1 : ringKrullDim S ≤ ((IsLocalRing.maximalIdeal S).spanFinrank : WithBot ℕ∞) := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := S)]
    exact_mod_cast hh
  refine (isRegularLocalRing_iff S).mpr (le_antisymm ?_ hle1)
  rw [hdim, ← hR]
  exact_mod_cast h4
end FunctorialResolution.EmbeddedResolution
