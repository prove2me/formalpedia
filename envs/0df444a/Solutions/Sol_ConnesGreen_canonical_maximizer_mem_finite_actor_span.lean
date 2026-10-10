-- Prove2me | solution 1 for ConnesGreen.canonical_maximizer_mem_finite_actor_span
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T13:22:38.224241+00:00
-- url     : https://prove2.me/submissions/309e57d3-2587-461d-b6c0-6765bf9feb77

import Definitions.Def_ConnesGreen_positive_endpoint_support

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
end ConnesGreen
theorem solution
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (hμ : canonicalCertificateThreshold t ht S ≠ 0) (x : Physical t)
    (hx : x ∈ canonicalMaximizingSpace t ht S)
    (hc : ∀ ρ : CriticalZeros, ρ ∉ F →
      ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) :
    x ∈ Submodule.span ℂ
      (Set.range (fun ρ : {ρ : CriticalZeros // ρ ∈ S} =>
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∪
       Set.range (fun ρ : {ρ : CriticalZeros // ρ ∈ F} =>
        positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1)) := by
  let V := Submodule.span ℂ
      (Set.range (fun ρ : {ρ : CriticalZeros // ρ ∈ S} =>
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∪
       Set.range (fun ρ : {ρ : CriticalZeros // ρ ∈ F} =>
        positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1))
  apply (V.smul_mem_iff (Complex.ofReal_ne_zero.mpr hμ)).mp
  rw [canonical_maximizer_finite_reconstruction t ht S F x hx hc]
  apply V.sub_mem
  · apply V.sum_mem
    intro ρ hρ
    apply V.smul_mem
    exact Submodule.subset_span (Set.mem_union_left _ ⟨⟨ρ, hρ⟩, rfl⟩)
  · apply V.sum_mem
    intro ρ hρ
    apply V.smul_mem
    exact Submodule.subset_span (Set.mem_union_right _ ⟨⟨ρ, hρ⟩, rfl⟩)
