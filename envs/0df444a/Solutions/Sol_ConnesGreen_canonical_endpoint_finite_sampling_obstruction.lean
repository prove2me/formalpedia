-- Prove2me | solution 1 for ConnesGreen.canonical_endpoint_finite_sampling_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T13:24:03.029657+00:00
-- url     : https://prove2.me/submissions/d6989195-78c8-4120-877c-0566f72b3cfa

import Definitions.Def_ConnesGreen_positive_endpoint_support

import Theorems.Thm_ConnesGreen_canonical_positive_threshold_attained
import Theorems.Thm_ConnesGreen_canonical_finite_certificate_neutral_tail_zero
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative
namespace ConnesGreen
theorem canonical_mem_maximizingSpace_iff (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (x : Physical t) :
    x ∈ canonicalMaximizingSpace t ht S ↔
      canonicalLossCovariance t ht S x = (canonicalCertificateThreshold t ht S : ℂ) • x :=
  Module.End.mem_eigenspace_iff
theorem canonical_positive_covariance_of_finite_profile
    (t : ℝ) (ht : 0 < t) (F : Finset CriticalZeros) (x : Physical t)
    (hc : ∀ ρ : CriticalZeros, ρ ∉ F →
      ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) :
    canonicalPositiveCovariance t ht x =
      ∑ ρ ∈ F, ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ •
        positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ := by
  simp only [canonicalPositiveCovariance, ContinuousLinearMap.comp_apply,
    canonicalPositiveSynthesis]
  rw [columnSynthesis_apply]
  simp_rw [columnSynthesis_adjoint_coordinate]
  exact tsum_eq_sum (fun ρ hρ => by rw [hc ρ hρ, zero_smul])
theorem canonical_selected_covariance_finite_sum
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) (x : Physical t) :
    (canonicalSelectedSynthesis t ht S) ((canonicalSelectedSynthesis t ht S).adjoint x) =
      ∑ ρ ∈ S, ⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ •
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ := by
  unfold canonicalSelectedSynthesis
  rw [columnSynthesis_apply]
  simp_rw [columnSynthesis_adjoint_coordinate]
  exact Finset.tsum_subtype S (fun ρ : CriticalZeros =>
    ⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ •
      negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ)
theorem canonical_maximizer_finite_reconstruction
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros) (x : Physical t)
    (hx : x ∈ canonicalMaximizingSpace t ht S)
    (hc : ∀ ρ : CriticalZeros, ρ ∉ F →
      ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) :
    (canonicalCertificateThreshold t ht S : ℂ) • x =
      (∑ ρ ∈ S, ⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ •
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) -
      ∑ ρ ∈ F, ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ •
        positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ := by
  rw [← (canonical_mem_maximizingSpace_iff t ht S x).mp hx]
  change (canonicalSelectedSynthesis t ht S) ((canonicalSelectedSynthesis t ht S).adjoint x) -
    canonicalPositiveCovariance t ht x = _
  rw [canonical_selected_covariance_finite_sum,
    canonical_positive_covariance_of_finite_profile t ht F x hc]
theorem canonicalLossCovariance_quadratic (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (x : Physical t) :
    RCLike.re ⟪canonicalLossCovariance t ht S x, x⟫_ℂ =
      ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 -
        ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 := by
  have hn := (canonicalSelectedSynthesis t ht S).adjoint.apply_norm_sq_eq_inner_adjoint_left x
  have hp := (canonicalPositiveSynthesis t ht).adjoint.apply_norm_sq_eq_inner_adjoint_left x
  simp only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply] at hn hp
  simp only [canonicalLossCovariance, canonicalPositiveCovariance,
    ContinuousLinearMap.sub_apply, inner_sub_left, map_sub, ContinuousLinearMap.comp_apply]
  rw [← hn, ← hp]
theorem canonical_maximizing_margin_zero (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (x : Physical t)
    (hx : x ∈ canonicalMaximizingSpace t ht S) : canonicalSharpMargin t ht S x = 0 := by
  have hq := canonicalLossCovariance_quadratic t ht S x
  have he := (canonical_mem_maximizingSpace_iff t ht S x).mp hx
  have hscalar : RCLike.re ⟪(canonicalCertificateThreshold t ht S : ℂ) • x, x⟫_ℂ =
      canonicalCertificateThreshold t ht S * ‖x‖ ^ 2 := by
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow, ← Complex.ofReal_mul]
  rw [he, hscalar] at hq
  unfold canonicalSharpMargin
  linarith
theorem canonical_endpoint_certificate_maximizing_custody
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (hμ : 0 < canonicalCertificateThreshold t ht S)
    (hF : 0 ≤ canonicalFiniteSelectedCorrection t ht S F (canonicalCertificateThreshold t ht S)) :
    ∀ x : Physical t, x ∈ canonicalMaximizingSpace t ht S →
      ∀ ρ : CriticalZeros, ρ ∉ F →
        ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0 := by
  intro x hx
  exact canonical_finite_certificate_neutral_tail_zero t ht S F _ hμ hF x
    (canonical_maximizing_margin_zero t ht S x hx)
end ConnesGreen
theorem solution
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (hμ : 0 < canonicalCertificateThreshold t ht S)
    (hF : 0 ≤ canonicalFiniteSelectedCorrection t ht S F (canonicalCertificateThreshold t ht S)) :
    ∃ x : Physical t, x ≠ 0 ∧
      (canonicalCertificateThreshold t ht S : ℂ) • x =
        (∑ ρ ∈ S, ⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ •
          negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) -
        (∑ ρ ∈ F, ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ •
          positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) ∧
      (∀ ρ : CriticalZeros, ρ ∉ F →
        ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) := by
  obtain ⟨x, hn, he, _⟩ := canonical_positive_threshold_attained t ht S hμ
  have hx := (canonical_mem_maximizingSpace_iff t ht S x).mpr he
  have hc := canonical_endpoint_certificate_maximizing_custody t ht S F hμ hF x hx
  exact ⟨x, hn, canonical_maximizer_finite_reconstruction t ht S F x hx hc, hc⟩
