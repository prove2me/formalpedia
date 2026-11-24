-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.map_derivIdealIterate_le_span_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:47:16.41916+00:00
-- url     : https://prove2.me/submissions/3ae0f361-8b37-456c-9431-49f6f9e30570

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealEtaleBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativesInBlowupCharts
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_map_derivIdeal_le_span_pow_mul
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_zero


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
    (J : Ideal S) (J₁ : Ideal S₁) (m : ℕ)
    (hJ : Ideal.map φ J ≤ Ideal.span {coord k ι S₁ s ^ m} * J₁)
    (j : ℕ) (hj : j ≤ m) :
    Ideal.map φ (derivIdealIterate k j J)
      ≤ Ideal.span {coord k ι S₁ s ^ (m - j)} * derivIdealIterate k j J₁ := by
  have key : ∀ r : ℕ, r ≤ m → Ideal.map φ (derivIdealIterate k r J)
      ≤ Ideal.span {coord k ι S₁ s ^ (m - r)} * derivIdealIterate k r J₁ := by
    intro r
    induction r with
    | zero =>
        intro _
        rw [derivIdealIterate_zero k J, derivIdealIterate_zero k J₁, Nat.sub_zero]
        exact hJ
    | succ r ih =>
        intro hr
        have hrm : r ≤ m := Nat.le_of_succ_le hr
        have h1 : 1 ≤ m - r := by omega
        have hstep := map_derivIdeal_le_span_pow_mul k ι S S₁ φ T s hin hs hout hsT hnzd
          (derivIdealIterate k r J) (derivIdealIterate k r J₁) (m - r) h1 (ih hrm)
        have hmm : m - r - 1 = m - (r + 1) := by omega
        rw [hmm] at hstep
        rw [derivIdealIterate_succ k r J, derivIdealIterate_succ k r J₁]
        exact hstep
  exact key j hj
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
