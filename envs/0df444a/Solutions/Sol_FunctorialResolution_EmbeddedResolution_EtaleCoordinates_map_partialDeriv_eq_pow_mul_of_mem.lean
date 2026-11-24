-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.map_partialDeriv_eq_pow_mul_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:11.282796+00:00
-- url     : https://prove2.me/submissions/7fc17217-aabc-4ee0-ba99-24d65c1c2228

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealEtaleBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativesInBlowupCharts
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDeriv_map_of_mem

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
    (f : S) (g : S₁) (e : ℕ) (hfg : φ f = coord k ι S₁ s ^ (e + 1) * g) :
    φ (partialDeriv k ι S i f) = coord k ι S₁ s ^ e * partialDeriv k ι S₁ i g := by
  have h1 : partialDeriv k ι S₁ i (φ f)
      = coord k ι S₁ s * φ (partialDeriv k ι S i f) :=
    partialDeriv_map_of_mem k ι S S₁ φ T s hin hs hout i hiT his f
  have hy : partialDeriv k ι S₁ i (coord k ι S₁ s) = 0 :=
    partialDeriv_coord_of_ne k ι S₁ i s his
  have hpow : partialDeriv k ι S₁ i (coord k ι S₁ s ^ (e + 1)) = 0 := by
    rw [Derivation.leibniz_pow, hy, smul_zero, smul_zero]
  rw [hfg, Derivation.leibniz, hpow, smul_zero, add_zero, smul_eq_mul] at h1
  have key : (φ (partialDeriv k ι S i f)
      - coord k ι S₁ s ^ e * partialDeriv k ι S₁ i g) * coord k ι S₁ s = 0 := by
    linear_combination -h1
  have h3 : φ (partialDeriv k ι S i f)
      - coord k ι S₁ s ^ e * partialDeriv k ι S₁ i g = 0 :=
    (mem_nonZeroDivisors_iff.mp hnzd).2 _ key
  linear_combination h3
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
