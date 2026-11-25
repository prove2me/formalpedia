-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.map_logDerivIdealIterate_le_span_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:23:11.876679+00:00
-- url     : https://prove2.me/submissions/472df723-da13-43e3-ad07-5eb61ddf4197

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativesInBlowupCharts
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativesInBlowupCharts
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_map_logDerivIdeal_le_span_pow_mul
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealIterate_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealIterate_zero


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
theorem _root_.solution [Fintype ι]
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hsT : s ∈ T) (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (i : ι) (hiT : i ∈ T) (his : i ≠ s)
    (J : Ideal S) (J₁ : Ideal S₁) (m : ℕ)
    (hJ : Ideal.map φ J ≤ Ideal.span {coord k ι S₁ s ^ m} * J₁)
    (j : ℕ) (hj : j ≤ m) :
    Ideal.map φ (logDerivIdealIterate k (Ideal.span {coord k ι S i}) j J)
      ≤ Ideal.span {coord k ι S₁ s ^ (m - j)}
          * logDerivIdealIterate k (Ideal.span {coord k ι S₁ i}) j J₁ := by
  revert hj
  induction j with
  | zero =>
      intro _
      rw [logDerivIdealIterate_zero, logDerivIdealIterate_zero, Nat.sub_zero]
      exact hJ
  | succ j ih =>
      intro hj
      have h1 := ih (Nat.le_of_succ_le hj)
      have h2 := map_logDerivIdeal_le_span_pow_mul k ι S S₁ φ T s hin hs hout hsT hnzd i hiT his
        (logDerivIdealIterate k (Ideal.span {coord k ι S i}) j J)
        (logDerivIdealIterate k (Ideal.span {coord k ι S₁ i}) j J₁) (m - j) (by omega) h1
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ]
      have hsub : m - j - 1 = m - (j + 1) := by omega
      rwa [hsub] at h2
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
