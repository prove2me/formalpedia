-- Prove2me | solution 1 for ConnesGreen.canonical_endpoint_integral_sampling_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T16:42:33.769466+00:00
-- url     : https://prove2.me/submissions/fe0a67fc-bc9a-4153-a64f-fda275ee2e68

import Definitions.Def_ConnesGreen_positive_endpoint_support
import Definitions.Def_ConnesGreen_integral_certificate_kernel

import Theorems.Thm_ConnesGreen_canonical_maximizer_iff_integral_sampling_kernel
import Theorems.Thm_ConnesGreen_canonical_positive_threshold_attained
import Theorems.Thm_ConnesGreen_canonical_finite_certificate_neutral_tail_zero
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative
namespace ConnesGreen
theorem canonical_mem_maximizingSpace_iff (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (x : Physical t) :
    x ∈ canonicalMaximizingSpace t ht S ↔
      canonicalLossCovariance t ht S x = (canonicalCertificateThreshold t ht S : ℂ) • x :=
  Module.End.mem_eigenspace_iff
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
    ∃ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
      canonicalFiniteColumnKernel t S F *ᵥ c ≠ 0 ∧
      canonicalFiniteIntegralCertificate t S F (canonicalCertificateThreshold t ht S) *ᵥ c = 0 ∧
      ∀ ρ : CriticalZeros, ρ ∉ F →
        (∑ j, (Sum.elim
          (fun σ : {σ : CriticalZeros // σ ∈ F} => canonicalPairGramKernel t 1 1 ρ σ.1)
          (fun σ : {σ : CriticalZeros // σ ∈ S} => canonicalPairGramKernel t 1 (-1) ρ σ.1) j) * c j) = 0 := by
  apply (canonical_maximizer_iff_integral_sampling_kernel t ht S F hμ.ne').mp
  obtain ⟨x, hn, he, _⟩ := canonical_positive_threshold_attained t ht S hμ
  have hx := (canonical_mem_maximizingSpace_iff t ht S x).mpr he
  exact ⟨x, hn, hx, canonical_endpoint_certificate_maximizing_custody t ht S F hμ hF x hx⟩
