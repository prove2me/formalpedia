-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDerivIdealIterate_controlledTransform_le_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:25:55.062462+00:00
-- url     : https://prove2.me/submissions/006776af-232f-4a97-95d1-7ef06f461f30

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativesInBlowupCharts
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PartialDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_ControlledTransformLogDerivativesInCharts
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDerivIdeal_biSup_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDerivIdeal_controlledTransform_le_sup
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDerivIdealIterate_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDerivIdealIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDerivIdeal_mono


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
    (hsT : s ∈ T)
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (hhT : h ∈ T) (hhs : h ≠ s)
    (J : Ideal S) (L : ℕ → Ideal S₁) (m : ℕ)
    (hL : ∀ i ≤ m,
      Ideal.span {coord k ι S₁ s ^ (m - i)} * L i = Ideal.map φ (derivIdealIterate k i J))
    (l : ℕ) (hl : l ≤ m) :
    partialDerivIdealIterate k ι S₁ h l (L 0) ≤ ⨆ i, ⨆ _ : i ≤ l, L i := by
  revert hl
  induction l with
  | zero =>
      intro _
      rw [partialDerivIdealIterate_zero]
      exact le_iSup₂ (f := fun i (_ : i ≤ 0) => L i) 0 le_rfl
  | succ l ih =>
      intro hl
      rw [partialDerivIdealIterate_succ]
      have hlm : l ≤ m := Nat.le_of_succ_le hl
      have h1 := ih hlm
      refine le_trans (partialDerivIdeal_mono k ι S₁ h h1) ?_
      refine le_trans (partialDerivIdeal_biSup_le k ι S₁ h l L) ?_
      refine iSup_le fun i => iSup_le fun hi => ?_
      have him : i < m := lt_of_le_of_lt hi (by omega)
      have hstep := partialDerivIdeal_controlledTransform_le_sup k ι S S₁ φ T s h
        hsT hin hs hout hnzd hhT hhs J L m hL i him
      refine hstep.trans (sup_le ?_ ?_)
      · exact le_iSup₂ (f := fun j (_ : j ≤ l + 1) => L j) i (by omega)
      · exact le_iSup₂ (f := fun j (_ : j ≤ l + 1) => L j) (i + 1) (by omega)
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
