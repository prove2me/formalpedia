-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDerivIdeal_controlledTransform_le_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:38:37.775338+00:00
-- url     : https://prove2.me/submissions/5cab4923-9000-4cd9-a904-a578cf213fd7

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativesInBlowupCharts
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PartialDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_ControlledTransformLogDerivativesInCharts
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDerivIdeal_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDeriv_mem_sup_of_span_pow_mul_eq_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_succ


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
  (φ : S →ₐ[k] S₁) (T : Finset ι) (s h : ι)
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution
    (_hsT : s ∈ T)
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (hhT : h ∈ T) (hhs : h ≠ s)
    (J : Ideal S) (L : ℕ → Ideal S₁) (m : ℕ)
    (hL : ∀ i ≤ m,
      Ideal.span {coord k ι S₁ s ^ (m - i)} * L i = Ideal.map φ (derivIdealIterate k i J))
    (i : ℕ) (hi : i < m) :
    partialDerivIdeal k ι S₁ h (L i) ≤ L i ⊔ L (i + 1) := by
  refine partialDerivIdeal_le k ι S₁ h le_sup_left ?_
  intro g hg
  have hc : m - i = (m - i - 1) + 1 := by omega
  have hJ : Ideal.span {coord k ι S₁ s ^ ((m - i - 1) + 1)} * L i
      = Ideal.map φ (derivIdealIterate k i J) := by
    rw [← hc]
    exact hL i (le_of_lt hi)
  have hD : Ideal.map φ (derivIdeal k (derivIdealIterate k i J)) ≤
      Ideal.span {coord k ι S₁ s ^ (m - i - 1)} * L (i + 1) := by
    have h2 := hL (i + 1) (by omega)
    have h3 : m - (i + 1) = m - i - 1 := by omega
    rw [h3] at h2
    rw [← derivIdealIterate_succ]
    exact le_of_eq h2.symm
  exact partialDeriv_mem_sup_of_span_pow_mul_eq_map k ι S S₁ φ T s hin hs hout hnzd h hhT hhs
    (derivIdealIterate k i J) (L i) (L (i + 1)) (m - i - 1) hJ hD g hg
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
