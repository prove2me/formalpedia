-- Prove2me | solution 1 for ConnesGreen.canonical_maximizer_iff_kernel_dimension_sampling
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T17:33:13.15376+00:00
-- url     : https://prove2.me/submissions/e54965d3-3c87-489f-8892-f23e4a612043

import Definitions.Def_ConnesGreen_integral_sampling_row
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

import Theorems.Thm_ConnesGreen_canonical_omitted_integral_rows_finite_on_certificate_kernel
import Theorems.Thm_ConnesGreen_canonical_maximizer_iff_integral_sampling_kernel
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability
theorem solution
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (hμ : canonicalCertificateThreshold t ht S ≠ 0) :
    ∃ G : Finset CriticalZeros, G.card ≤ Module.finrank ℂ
      (LinearMap.ker (canonicalFiniteIntegralCertificate t S F
        (canonicalCertificateThreshold t ht S)).mulVecLin) ∧
      (∀ ρ ∈ G, ρ ∉ F) ∧
      ((∃ x : Physical t, x ≠ 0 ∧ x ∈ canonicalMaximizingSpace t ht S ∧
        ∀ ρ : CriticalZeros, ρ ∉ F →
          ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) ↔
      (∃ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
        canonicalFiniteColumnKernel t S F *ᵥ c ≠ 0 ∧
        canonicalFiniteIntegralCertificate t S F (canonicalCertificateThreshold t ht S) *ᵥ c = 0 ∧
        ∀ ρ ∈ G, canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0)) := by
  obtain ⟨G, hcard, hG, hrows⟩ := canonical_omitted_integral_rows_finite_on_certificate_kernel t S F
    (canonicalCertificateThreshold t ht S)
  refine ⟨G, hcard, hG, ?_⟩
  rw [canonical_maximizer_iff_integral_sampling_kernel t ht S F hμ]
  apply exists_congr
  intro c
  apply and_congr_right
  intro _
  apply and_congr_right
  intro hc
  simpa only [canonicalIntegralSamplingRow, dotProduct] using (hrows c hc).symm
