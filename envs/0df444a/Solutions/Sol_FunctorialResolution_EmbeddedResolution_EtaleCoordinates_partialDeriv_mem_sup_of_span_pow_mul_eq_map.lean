-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDeriv_mem_sup_of_span_pow_mul_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:46:34.894923+00:00
-- url     : https://prove2.me/submissions/d00b18ea-cb8f-469d-be35-69c671b8ba57

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativesInBlowupCharts
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativesInBlowupCharts
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDeriv_map_of_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_of_mem_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S₁ : Type*) [CommRing S₁] [Algebra k S₁] [Algebra (MvPolynomial ι k) S₁]
  [IsScalarTower k (MvPolynomial ι k) S₁] [Algebra.FormallyEtale (MvPolynomial ι k) S₁]
  (φ : S →ₐ[k] S₁) (T : Finset ι) (s : ι)
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (i : ι) (hiT : i ∈ T) (his : i ≠ s)
    (J : Ideal S) (L L' : Ideal S₁) (c : ℕ)
    (hJ : Ideal.span {coord k ι S₁ s ^ (c + 1)} * L = Ideal.map φ J)
    (hD : Ideal.map φ (derivIdeal k J) ≤ Ideal.span {coord k ι S₁ s ^ c} * L')
    (g : S₁) (hg : g ∈ L) :
    partialDeriv k ι S₁ i g ∈ L ⊔ L' := by
  have hmapspan : Ideal.span (⇑φ '' (J : Set S)) = Ideal.map φ J := by
    rw [← Ideal.map_span, Ideal.span_eq]
  have hgen : ∀ x ∈ (⇑φ '' (J : Set S)),
      partialDeriv k ι S₁ i x ∈ Ideal.span {coord k ι S₁ s ^ (c + 1)} * (L ⊔ L') := by
    rintro _ ⟨f, hf, rfl⟩
    have h1 : partialDeriv k ι S₁ i (φ f)
        = coord k ι S₁ s * φ (partialDeriv k ι S i f) :=
      partialDeriv_map_of_mem k ι S S₁ φ T s hin hs hout i hiT his f
    have h2 : φ (partialDeriv k ι S i f) ∈ Ideal.map φ (derivIdeal k J) :=
      Ideal.mem_map_of_mem φ
        (derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) (SetLike.mem_coe.mp hf))
    obtain ⟨z, hz, hzeq⟩ := Ideal.mem_span_singleton_mul.mp (hD h2)
    rw [h1, ← hzeq]
    exact Ideal.mem_span_singleton_mul.mpr ⟨z, Submodule.mem_sup_right hz, by ring⟩
  have hGT : Ideal.span (⇑φ '' (J : Set S))
      ≤ Ideal.span {coord k ι S₁ s ^ (c + 1)} * (L ⊔ L') := by
    rw [hmapspan, ← hJ]
    exact Ideal.mul_mono_right le_sup_left
  have hmem : coord k ι S₁ s ^ (c + 1) * g ∈ Ideal.span (⇑φ '' (J : Set S)) := by
    rw [hmapspan, ← hJ]
    exact Ideal.mem_span_singleton_mul.mpr ⟨g, hg, rfl⟩
  have key := derivation_apply_mem_of_mem_span (partialDeriv k ι S₁ i) hGT hgen hmem
  have hDy : partialDeriv k ι S₁ i (coord k ι S₁ s) = 0 :=
    partialDeriv_coord_of_ne k ι S₁ i s his
  have hDypow : partialDeriv k ι S₁ i (coord k ι S₁ s ^ (c + 1)) = 0 := by
    rw [Derivation.leibniz_pow, hDy, smul_zero, smul_zero]
  have hexp : partialDeriv k ι S₁ i (coord k ι S₁ s ^ (c + 1) * g)
      = coord k ι S₁ s ^ (c + 1) * partialDeriv k ι S₁ i g := by
    rw [Derivation.leibniz, hDypow, smul_zero, add_zero, smul_eq_mul]
  rw [hexp] at key
  obtain ⟨w, hw, hweq⟩ := Ideal.mem_span_singleton_mul.mp key
  have hnz : coord k ι S₁ s ^ (c + 1) ∈ nonZeroDivisors S₁ := pow_mem hnzd (c + 1)
  have h0 : (partialDeriv k ι S₁ i g - w) * coord k ι S₁ s ^ (c + 1) = 0 := by
    linear_combination -hweq
  have h1 : partialDeriv k ι S₁ i g - w = 0 :=
    (mem_nonZeroDivisors_iff.mp hnz).2 _ h0
  have h2 : partialDeriv k ι S₁ i g = w := sub_eq_zero.mp h1
  rw [h2]
  exact hw
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
