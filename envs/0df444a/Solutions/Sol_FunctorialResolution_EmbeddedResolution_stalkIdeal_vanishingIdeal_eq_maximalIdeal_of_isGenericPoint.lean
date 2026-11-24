-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_vanishingIdeal_eq_maximalIdeal_of_isGenericPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:51:26.241917+00:00
-- url     : https://prove2.me/submissions/2d63fe79-69be-49db-b7a6-04163493edfa

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_map_germ
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineOpens_mem

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
private theorem mem_of_vanishingIdeal_le {R : Type*} [CommRing R]
    (W : Set (PrimeSpectrum R)) (hW : IsClosed W) (q : PrimeSpectrum R)
    (h : PrimeSpectrum.vanishingIdeal W ≤ q.asIdeal) : q ∈ W := by
  have h0 : q ∈ PrimeSpectrum.zeroLocus
      ((PrimeSpectrum.vanishingIdeal W : Ideal R) : Set R) :=
    (PrimeSpectrum.mem_zeroLocus _ _).mpr (fun y hy => h hy)
  rwa [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hW.closure_eq] at h0
private theorem map_algebraMap_eq_maximalIdeal {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing S] (p : Ideal R) [p.IsPrime] [IsLocalization p.primeCompl S]
    (J : Ideal R) (hJ : J.IsRadical) (hJp : J ≤ p)
    (hmin : ∀ q : Ideal R, q.IsPrime → J ≤ q → q ≤ p → q = p) :
    Ideal.map (algebraMap R S) J = IsLocalRing.maximalIdeal S := by
  have hmap : Ideal.map (algebraMap R S) p = IsLocalRing.maximalIdeal S :=
    IsLocalization.AtPrime.map_eq_maximalIdeal ..
  have hcomap_le : Ideal.comap (algebraMap R S) (IsLocalRing.maximalIdeal S) ≤ p := by
    intro r hr
    by_contra hrp
    rw [Ideal.mem_comap] at hr
    have hrp' : r ∈ p.primeCompl := hrp
    have hunit : IsUnit (algebraMap R S r) := IsLocalization.map_units S ⟨r, hrp'⟩
    have hnu := (IsLocalRing.mem_maximalIdeal _).mp hr
    rw [mem_nonunits_iff] at hnu
    exact hnu hunit
  refine le_antisymm (le_trans (Ideal.map_mono hJp) (le_of_eq hmap)) ?_
  have hle : IsLocalRing.maximalIdeal S ≤ (Ideal.map (algebraMap R S) J).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hPle, hPprime⟩
    have : P.IsPrime := hPprime
    have hPmax : P ≤ IsLocalRing.maximalIdeal S := IsLocalRing.le_maximalIdeal hPprime.ne_top
    have h1 : Ideal.comap (algebraMap R S) P = p := by
      refine hmin _ (Ideal.comap_isPrime (algebraMap R S) P) ?_ ?_
      · rw [← Ideal.map_le_iff_le_comap]
        exact hPle
      · exact le_trans (Ideal.comap_mono hPmax) hcomap_le
    have heq : IsLocalRing.maximalIdeal S = P := by
      rw [← hmap, ← h1]
      exact IsLocalization.map_under p.primeCompl S P
    exact heq.le
  refine hle.trans ?_
  rw [← IsLocalization.map_radical p.primeCompl S J]
  exact Ideal.map_mono hJ
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (Z : TopologicalSpace.Closeds X) (ξ : X)
    (T : Set X) (hT : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (Z : Set X)) T)
    (hξ : IsGenericPoint ξ T) :
    stalkIdeal (Scheme.IdealSheafData.vanishingIdeal Z) ξ
      = IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) := by
  obtain ⟨U, hxU0⟩ := X.exists_affineOpens_mem ξ
  have hxU : ξ ∈ U.1 := hxU0
  have hU : IsAffineOpen U.1 := U.2
  have hZcl : IsClosed (Z : Set X) := Z.2
  have hcont : Continuous (⇑(hU.fromSpec)) := (hU.fromSpec).continuous
  have hξT : ξ ∈ T := by
    rw [← hξ]
    exact subset_closure (Set.mem_singleton ξ)
  have hξZ : ξ ∈ (Z : Set X) := hT.1.2 hξT
  have hWclosed : IsClosed ((⇑hU.fromSpec ⁻¹' (Z : Set X)) : Set (PrimeSpectrum Γ(X, U.1))) :=
    hZcl.preimage hcont
  have hJdef : (Scheme.IdealSheafData.vanishingIdeal Z).ideal U
      = PrimeSpectrum.vanishingIdeal (⇑hU.fromSpec ⁻¹' (Z : Set X)) := rfl
  have hfp : (⇑(hU.fromSpec)) (hU.primeIdealOf ⟨ξ, hxU⟩) = ξ :=
    hU.fromSpec_primeIdealOf ⟨ξ, hxU⟩
  have hmemW : hU.primeIdealOf ⟨ξ, hxU⟩ ∈ (⇑(hU.fromSpec) ⁻¹' (Z : Set X)) := by
    show (⇑(hU.fromSpec)) (hU.primeIdealOf ⟨ξ, hxU⟩) ∈ (Z : Set X)
    rw [hfp]
    exact hξZ
  rw [stalkIdeal_eq_map_germ _ ξ U hxU, hJdef]
  let germAlgebra : Algebra Γ(X, U.1) (X.presheaf.stalk ξ) :=
    (X.presheaf.germ U.1 ξ hxU).hom.toAlgebra
  have hloc : IsLocalization (hU.primeIdealOf ⟨ξ, hxU⟩).asIdeal.primeCompl
      (X.presheaf.stalk ξ) := hU.isLocalization_stalk ⟨ξ, hxU⟩
  have halg : (X.presheaf.germ U.1 ξ hxU).hom
      = algebraMap Γ(X, U.1) (X.presheaf.stalk ξ) := rfl
  rw [halg]
  refine map_algebraMap_eq_maximalIdeal (hU.primeIdealOf ⟨ξ, hxU⟩).asIdeal _
    (PrimeSpectrum.isRadical_vanishingIdeal _) ?_ ?_
  · intro f hf
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp hf _ hmemW
  · intro q hq hJq hqp
    have hQW : (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ∈
        ((⇑hU.fromSpec ⁻¹' (Z : Set X)) : Set (PrimeSpectrum Γ(X, U.1))) :=
      mem_of_vanishingIdeal_le _ hWclosed ⟨q, hq⟩ hJq
    have hQP : (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ⤳ hU.primeIdealOf ⟨ξ, hxU⟩ := by
      rw [specializes_iff_mem_closure, PrimeSpectrum.closure_singleton,
        PrimeSpectrum.mem_zeroLocus]
      exact fun y hy => hqp hy
    have hzspec : (⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ⤳ ξ := by
      have hmapped := hQP.map hcont
      rwa [hfp] at hmapped
    have hzZ : (⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ∈ (Z : Set X) := hQW
    have hirr : IsIrreducible
        (closure {(⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))}) :=
      isIrreducible_singleton.closure
    have hsubZ : closure {(⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))} ⊆ (Z : Set X) :=
      hZcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hzZ)
    have hTsub : T ⊆ closure {(⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))} := by
      rw [← hξ]
      exact closure_minimal
        (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hzspec)) isClosed_closure
    have hmax := hT.2 ⟨hirr, hsubZ⟩ hTsub
    have hzT : (⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ∈ T :=
      hmax (subset_closure (Set.mem_singleton _))
    have hξz : ξ ⤳ (⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) :=
      specializes_iff_mem_closure.mpr (by rw [hξ]; exact hzT)
    have hind : Topology.IsInducing (⇑(hU.fromSpec)) :=
      (hU.fromSpec).isOpenEmbedding.toIsEmbedding.toIsInducing
    have h3 : (⇑(hU.fromSpec)) (hU.primeIdealOf ⟨ξ, hxU⟩) ⤳
        (⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) := by
      rw [hfp]
      exact hξz
    have hPQ : hU.primeIdealOf ⟨ξ, hxU⟩ ⤳ (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) :=
      hind.specializes_iff.mp h3
    have hpq : (hU.primeIdealOf ⟨ξ, hxU⟩).asIdeal ≤ q := by
      have h2 := specializes_iff_mem_closure.mp hPQ
      rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus] at h2
      exact fun y hy => h2 hy
    exact le_antisymm hqp hpq
end FunctorialResolution.EmbeddedResolution
