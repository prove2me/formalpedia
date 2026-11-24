-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.DerivIdealBaseChange.partialDeriv_mem_map_derivIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:46:34.98525+00:00
-- url     : https://prove2.me/submissions/3a79680b-30fe-48bb-958b-68e97709bbbf

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealEtaleBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealFieldExtension
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_DerivIdealBaseChange_partialDeriv_algHom_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_of_mem_span
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.DerivIdealBaseChange
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (L : Type*) [CommRing L] [Algebra k L]
  (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S' : Type*) [CommRing S'] [Algebra L S'] [Algebra (MvPolynomial ι L) S']
  [IsScalarTower L (MvPolynomial ι L) S'] [Algebra.FormallyEtale (MvPolynomial ι L) S']
  [Algebra k S'] [IsScalarTower k L S']
namespace FunctorialResolution.EmbeddedResolution.DerivIdealBaseChange
theorem _root_.solution (φ : S →ₐ[k] S')
    (hφ : ∀ i : ι, φ (coord k ι S i) = coord L ι S' i) (i : ι) (J : Ideal S)
    {g : S'} (hg : g ∈ Ideal.map φ J) :
    partialDeriv L ι S' i g ∈ Ideal.map φ (derivIdeal k J) := by
  have hle : Ideal.map φ J ≤ Ideal.span (⇑φ '' (J : Set S)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap]
    exact Ideal.subset_span ⟨y, hy, rfl⟩
  have hGT : Ideal.span (⇑φ '' (J : Set S)) ≤ Ideal.map φ (derivIdeal k J) := by
    rw [Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact Ideal.mem_map_of_mem φ (le_derivIdeal k J (show y ∈ J from hy))
  have hD : ∀ z ∈ (⇑φ '' (J : Set S)),
      partialDeriv L ι S' i z ∈ Ideal.map φ (derivIdeal k J) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [partialDeriv_algHom_apply (k := k) (L := L) (ι := ι) (S := S) (S' := S') φ hφ i y]
    exact Ideal.mem_map_of_mem φ
      (derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) (show y ∈ J from hy))
  exact derivation_apply_mem_of_mem_span (partialDeriv L ι S' i) hGT hD (hle hg)
end FunctorialResolution.EmbeddedResolution.DerivIdealBaseChange
