-- Prove2me | solution 1 for ConnesGreen.canonical_maximizer_iff_packet_bounded_sampling
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T20:14:53.066519+00:00
-- url     : https://prove2.me/submissions/f275b005-2370-4f6f-ba73-dcebdc477aea

import Definitions.Def_ConnesGreen_integral_sampling_row
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

import Theorems.Thm_ConnesGreen_canonical_omitted_integral_rows_finite_packet_bound
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
    (hμ : 0 < canonicalCertificateThreshold t ht S) :
    ∃ G : Finset CriticalZeros, G.card ≤ S.card ∧
      (∀ ρ ∈ G, ρ ∉ F) ∧
      ((∃ x : Physical t, x ≠ 0 ∧ x ∈ canonicalMaximizingSpace t ht S ∧
        ∀ ρ : CriticalZeros, ρ ∉ F →
          ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) ↔
      (∃ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
        canonicalFiniteColumnKernel t S F *ᵥ c ≠ 0 ∧
        canonicalFiniteIntegralCertificate t S F (canonicalCertificateThreshold t ht S) *ᵥ c = 0 ∧
        ∀ ρ ∈ G, canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0)) := by
  obtain ⟨G, hcard, hG, hrows⟩ := canonical_omitted_integral_rows_finite_packet_bound t ht S F
    (canonicalCertificateThreshold t ht S) hμ
  refine ⟨G, hcard, hG, ?_⟩
  rw [canonical_maximizer_iff_integral_sampling_kernel t ht S F (ne_of_gt hμ)]
  apply exists_congr
  intro c
  apply and_congr_right
  intro _
  apply and_congr_right
  intro hc
  simpa only [canonicalIntegralSamplingRow, dotProduct] using (hrows c hc).symm
