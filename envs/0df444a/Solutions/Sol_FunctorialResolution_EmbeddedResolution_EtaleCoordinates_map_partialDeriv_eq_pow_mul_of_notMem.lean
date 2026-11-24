-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.map_partialDeriv_eq_pow_mul_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:59:01.201226+00:00
-- url     : https://prove2.me/submissions/76354739-501d-4d80-90f9-979d9d2f9c45

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealEtaleBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativesInBlowupCharts
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDeriv_map_of_notMem

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
    (hsT : s ∈ T) (i : ι) (hiT : i ∉ T)
    (f : S) (g : S₁) (e : ℕ) (hfg : φ f = coord k ι S₁ s ^ (e + 1) * g) :
    φ (partialDeriv k ι S i f) = coord k ι S₁ s ^ (e + 1) * partialDeriv k ι S₁ i g := by
  have his : i ≠ s := fun h => hiT (by rw [h]; exact hsT)
  have hz : partialDeriv k ι S₁ i (coord k ι S₁ s) = 0 :=
    partialDeriv_coord_of_ne k ι S₁ i s his
  have hpow : partialDeriv k ι S₁ i (coord k ι S₁ s ^ (e + 1)) = 0 := by
    rw [Derivation.leibniz_pow, hz, smul_zero, smul_zero]
  rw [← partialDeriv_map_of_notMem k ι S S₁ φ T s hin hs hout hsT i hiT f, hfg,
    Derivation.leibniz, hpow, smul_zero, add_zero, smul_eq_mul]
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
