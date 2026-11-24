-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.map_partialDeriv_self_eq_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:16:09.142923+00:00
-- url     : https://prove2.me/submissions/0297f280-6ad9-4747-9ec7-34be02975e63

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealEtaleBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativesInBlowupCharts
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_mul_partialDeriv_map_eq_map_add_sum_erase
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_map_partialDeriv_eq_pow_mul_of_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply



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
    (hsT : s ∈ T) (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (f : S) (g : S₁) (e : ℕ) (hfg : φ f = coord k ι S₁ s ^ (e + 1) * g) :
    φ (partialDeriv k ι S s f)
      = coord k ι S₁ s ^ e
        * (coord k ι S₁ s * partialDeriv k ι S₁ s g + ((e + 1 : ℕ) : S₁) * g
            - ∑ i ∈ T.erase s, coord k ι S₁ i * partialDeriv k ι S₁ i g) := by
  have hpow : partialDeriv k ι S₁ s (coord k ι S₁ s ^ (e + 1))
      = ((e + 1 : ℕ) : S₁) * coord k ι S₁ s ^ e := by
    rw [Derivation.leibniz_pow, partialDeriv_coord_self, Nat.add_sub_cancel]
    simp only [smul_eq_mul, mul_one, nsmul_eq_mul]
  have h2 : partialDeriv k ι S₁ s (φ f)
      = coord k ι S₁ s ^ (e + 1) * partialDeriv k ι S₁ s g
        + ((e + 1 : ℕ) : S₁) * coord k ι S₁ s ^ e * g := by
    rw [hfg, Derivation.leibniz, hpow]
    simp only [smul_eq_mul]
    ring
  have hsum2 : ∑ i ∈ T.erase s, φ (coord k ι S i * partialDeriv k ι S i f)
      = coord k ι S₁ s ^ (e + 1)
        * ∑ i ∈ T.erase s, coord k ι S₁ i * partialDeriv k ι S₁ i g := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiT : i ∈ T := Finset.mem_of_mem_erase hi
    have his : i ≠ s := Finset.ne_of_mem_erase hi
    rw [map_mul, hin i hiT his,
      map_partialDeriv_eq_pow_mul_of_mem k ι S S₁ φ T s hin hs hout hnzd i hiT his f g e hfg]
    ring
  have h1 : coord k ι S₁ s * partialDeriv k ι S₁ s (φ f)
      = coord k ι S₁ s * φ (partialDeriv k ι S s f)
        + coord k ι S₁ s ^ (e + 1)
          * ∑ i ∈ T.erase s, coord k ι S₁ i * partialDeriv k ι S₁ i g := by
    rw [coord_mul_partialDeriv_map_eq_map_add_sum_erase k ι S S₁ φ T s hin hs hout hsT f, map_add, map_mul, hs, map_sum, hsum2]
  rw [h2] at h1
  have h0 : (φ (partialDeriv k ι S s f)
      - coord k ι S₁ s ^ e
        * (coord k ι S₁ s * partialDeriv k ι S₁ s g + ((e + 1 : ℕ) : S₁) * g
            - ∑ i ∈ T.erase s, coord k ι S₁ i * partialDeriv k ι S₁ i g))
      * coord k ι S₁ s = 0 := by
    linear_combination -h1
  have h3 := (mem_nonZeroDivisors_iff.mp hnzd).2 _ h0
  linear_combination h3
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
