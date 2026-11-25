-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.derivIdealIterate_le_iSup_logDerivIdealIterate_controlledTransform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:32:33.766418+00:00
-- url     : https://prove2.me/submissions/90763844-d3bf-430e-b955-b422f8e79c21

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativesInBlowupCharts
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PartialDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_ControlledTransformLogDerivativesInCharts
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDerivIdealIterate_controlledTransform_le_iSup
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_derivIdealIterate_le_iSup_logDerivIdealIterate_partialDerivIdealIterate
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealIterate_iSup_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealIterate_le_of_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealIterate_mono


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
theorem _root_.solution [Fintype ι]
    (hsT : s ∈ T)
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (hhT : h ∈ T) (hhs : h ≠ s)
    (J : Ideal S) (L : ℕ → Ideal S₁) (m : ℕ)
    (hL : ∀ i ≤ m,
      Ideal.span {coord k ι S₁ s ^ (m - i)} * L i = Ideal.map φ (derivIdealIterate k i J))
    (n : ℕ) (hn : n ≤ m) :
    derivIdealIterate k n (L 0) ≤
      ⨆ i, ⨆ _ : i ≤ n,
        logDerivIdealIterate k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - i) (L i) := by
  refine (derivIdealIterate_le_iSup_logDerivIdealIterate_partialDerivIdealIterate k ι S₁ h n (L 0)).trans ?_
  refine iSup_le fun l => iSup_le fun hln => ?_
  have hlm : l ≤ m := hln.trans hn
  have h1 : partialDerivIdealIterate k ι S₁ h l (L 0) ≤ ⨆ i, ⨆ _ : i ≤ l, L i :=
    partialDerivIdealIterate_controlledTransform_le_iSup k ι S S₁ φ T s h
      hsT hin hs hout hnzd hhT hhs J L m hL l hlm
  refine (logDerivIdealIterate_mono k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - l) h1).trans ?_
  refine (logDerivIdealIterate_iSup_le k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - l)
    (fun i => ⨆ _ : i ≤ l, L i)).trans ?_
  refine iSup_le fun i => ?_
  refine (logDerivIdealIterate_iSup_le k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - l)
    (fun _ : i ≤ l => L i)).trans ?_
  refine iSup_le fun hi => ?_
  have h2 : logDerivIdealIterate k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - l) (L i) ≤
      logDerivIdealIterate k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - i) (L i) :=
    logDerivIdealIterate_le_of_le k (Ideal.span ({coord k ι S₁ h} : Set S₁))
      (by omega : n - l ≤ n - i) (L i)
  exact h2.trans (le_iSup₂
    (f := fun j (_ : j ≤ n) =>
      logDerivIdealIterate k (Ideal.span ({coord k ι S₁ h} : Set S₁)) (n - j) (L j))
    i (hi.trans hln))
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
