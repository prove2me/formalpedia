-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.not_irreducibleComponent_subset_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:26.269382+00:00
-- url     : https://prove2.me/submissions/62a4899a-a78f-4e42-97f9-019fe9f6cf1a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_CartierDivisorComponents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem mem_closure_singleton_iff_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (a b : PrimeSpectrum Γ(X, U)) :
    a ∈ closure ({b} : Set (PrimeSpectrum Γ(X, U))) ↔
      hU.fromSpec a ∈ closure ({hU.fromSpec b} : Set (X : Type u)) := by
  have hoi : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hind := (Scheme.Hom.isOpenEmbedding hU.fromSpec).toIsEmbedding.toIsInducing
  constructor
  · intro hab
    have h1 : b ⤳ a := specializes_iff_mem_closure.mpr hab
    exact specializes_iff_mem_closure.mp (hind.specializes_iff.mpr h1)
  · intro hab
    have h1 : hU.fromSpec b ⤳ hU.fromSpec a := specializes_iff_mem_closure.mpr hab
    exact specializes_iff_mem_closure.mp (hind.specializes_iff.mp h1)
private theorem mem_primeIdealOf_of_notMem_basicOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {x : (X : Type u)} (hx : x ∈ U) {f : Γ(X, U)}
    (hb : x ∉ X.basicOpen f) : f ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  by_contra hfn
  apply hb
  have h1 : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
    rw [hU.fromSpec_preimage_basicOpen f]
    exact (PrimeSpectrum.mem_basicOpen f _).mpr hfn
  have h2 : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f := h1
  rw [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h2
  exact h2
private theorem mem_primeIdealOf_of_mem_support {X : Scheme.{u}} {I : X.IdealSheafData}
    {U : X.affineOpens} {x : (X : Type u)} (hx : x ∈ U.1) {f : Γ(X, U.1)}
    (hf : f ∈ I.ideal U) (hxs : x ∈ I.support) :
    f ∈ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have hz : x ∈ X.zeroLocus (I.ideal U : Set Γ(X, U.1)) :=
    (Scheme.IdealSheafData.mem_support_iff_of_mem hx).mp hxs
  rw [Scheme.mem_zeroLocus_iff] at hz
  exact mem_primeIdealOf_of_notMem_basicOpen U.2 hx (hz f hf)
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
namespace _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
theorem _root_.solution
    {X : Scheme.{u}} {D : X.IdealSheafData} (hD : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor D)
    {Z : Set (X : Type u)} (hZ : Z ∈ irreducibleComponents (X : Type u)) :
    ¬ Z ⊆ (D.support : Set (X : Type u)) := by
  intro hsub
  have hZcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hZ.1 hZcl
  have hξ' : closure ({ξ} : Set (X : Type u)) = Z := hξ
  have hξZ : ξ ∈ Z := by rw [← hξ']; exact subset_closure rfl
  obtain ⟨U, f, hxU, hf, hDU⟩ := hD ξ
  have hfD : f ∈ D.ideal U := by rw [hDU]; exact Ideal.subset_span rfl
  have hfp : f ∈ (U.2.primeIdealOf ⟨ξ, hxU⟩).asIdeal :=
    EmbeddedResolution.mem_primeIdealOf_of_mem_support hxU hfD (hsub hξZ)
  have hmin : (U.2.primeIdealOf ⟨ξ, hxU⟩).asIdeal ∈ minimalPrimes Γ(X, U.1) := by
    refine ⟨⟨(U.2.primeIdealOf ⟨ξ, hxU⟩).isPrime, bot_le⟩, ?_⟩
    rintro q ⟨hq, -⟩ hqle
    have hqle' : (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ≤ U.2.primeIdealOf ⟨ξ, hxU⟩ := hqle
    have hxy : (U.2.primeIdealOf ⟨ξ, hxU⟩) ∈
        closure ({(⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))} : Set (PrimeSpectrum Γ(X, U.1))) :=
      (PrimeSpectrum.le_iff_mem_closure ⟨q, hq⟩ (U.2.primeIdealOf ⟨ξ, hxU⟩)).mp hqle'
    have hξcl : ξ ∈ closure ({U.2.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))}
        : Set (X : Type u)) := by
      have h2 := (_root_.FunctorialResolution.EmbeddedResolution.mem_closure_singleton_iff_fromSpec U.2 (U.2.primeIdealOf ⟨ξ, hxU⟩) ⟨q, hq⟩).mp hxy
      rw [U.2.fromSpec_primeIdealOf ⟨ξ, hxU⟩] at h2
      exact h2
    have hZsub : Z ⊆ closure ({U.2.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))}
        : Set (X : Type u)) := by
      rw [← hξ']
      exact closure_minimal (Set.singleton_subset_iff.mpr hξcl) isClosed_closure
    have hyZ : U.2.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ∈ Z :=
      hZ.2 isIrreducible_singleton.closure hZsub (subset_closure rfl)
    have hy : U.2.fromSpec (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))
        ∈ closure ({ξ} : Set (X : Type u)) := by
      rw [hξ']; exact hyZ
    have hprimeLe : (U.2.primeIdealOf ⟨ξ, hxU⟩) ≤ (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) := by
      refine (PrimeSpectrum.le_iff_mem_closure (U.2.primeIdealOf ⟨ξ, hxU⟩) ⟨q, hq⟩).mpr ?_
      refine (_root_.FunctorialResolution.EmbeddedResolution.mem_closure_singleton_iff_fromSpec U.2 ⟨q, hq⟩ (U.2.primeIdealOf ⟨ξ, hxU⟩)).mpr ?_
      rw [U.2.fromSpec_primeIdealOf ⟨ξ, hxU⟩]
      exact hy
    exact hprimeLe
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hfp hmin hf
end _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
end FunctorialResolution.EmbeddedResolution
