-- Prove2me | solution 1 for ConnesGreen.canonical_integral_kernel_uniqueness_iff_finite_witness
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T17:12:23.693882+00:00
-- url     : https://prove2.me/submissions/c8b540cf-596b-45ad-a007-7cd62f6338ed

import Definitions.Def_ConnesGreen_integral_sampling_row

import Theorems.Thm_ConnesGreen_canonical_omitted_integral_rows_finite
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability
theorem solution
    (t : ℝ) (S F : Finset CriticalZeros) (δ : ℝ) :
    (∀ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
      canonicalFiniteIntegralCertificate t S F δ *ᵥ c = 0 →
      (∀ ρ : CriticalZeros, ρ ∉ F → canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) →
      canonicalFiniteColumnKernel t S F *ᵥ c = 0) ↔
    (∃ G : Finset CriticalZeros, G.card ≤ F.card + S.card ∧
      (∀ ρ ∈ G, ρ ∉ F) ∧
      ∀ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
        canonicalFiniteIntegralCertificate t S F δ *ᵥ c = 0 →
        (∀ ρ ∈ G, canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) →
        canonicalFiniteColumnKernel t S F *ᵥ c = 0) := by
  constructor
  · intro h
    obtain ⟨G, hcard, hG, hrows⟩ := canonical_omitted_integral_rows_finite t S F
    exact ⟨G, hcard, hG, fun c hk hr => h c hk ((hrows c).mp hr)⟩
  · rintro ⟨G, _, hG, h⟩ c hk hr
    exact h c hk (fun ρ hρ => hr ρ (hG ρ hρ))
