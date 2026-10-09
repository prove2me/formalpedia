-- Prove2me | solution 1 for ConnesGreen.canonical_positive_endpoint_certificate_eigenvector_custody
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T06:05:52.079795+00:00
-- url     : https://prove2.me/submissions/84c4bc63-54d2-4fe6-a3f6-efd282335194

import Definitions.Def_ConnesGreen_selected_loss_covariance
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

import Theorems.Thm_ConnesGreen_canonical_positive_threshold_attained
import Theorems.Thm_ConnesGreen_canonical_finite_certificate_neutral_tail_zero
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open ConnesGreen WeilDefect WeilDefect.ConnesNative
open ContinuousFunctionalCalculus
namespace ConnesGreen
end ConnesGreen
theorem solution
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (hμ : 0 < canonicalCertificateThreshold t ht S)
    (hF : 0 ≤ canonicalFiniteSelectedCorrection t ht S F
      (canonicalCertificateThreshold t ht S)) :
    ∃ x : Physical t, x ≠ 0 ∧
      canonicalLossCovariance t ht S x = (canonicalCertificateThreshold t ht S : ℂ) • x ∧
      (‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
        ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 +
          canonicalCertificateThreshold t ht S * ‖x‖ ^ 2 = 0) ∧
      ∀ ρ : CriticalZeros, ρ ∉ F →
        ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0 := by
  obtain ⟨x, hx, he, hn⟩ := canonical_positive_threshold_attained t ht S hμ
  exact ⟨x, hx, he, hn,
    canonical_finite_certificate_neutral_tail_zero t ht S F _ hμ hF x hn⟩
