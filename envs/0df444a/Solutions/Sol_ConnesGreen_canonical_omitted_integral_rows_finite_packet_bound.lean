-- Prove2me | solution 1 for ConnesGreen.canonical_omitted_integral_rows_finite_packet_bound
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T20:11:21.931916+00:00
-- url     : https://prove2.me/submissions/20561c1e-f8d4-4559-956b-9467ff06f3eb

import Definitions.Def_ConnesGreen_integral_sampling_row
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

import Theorems.Thm_ConnesGreen_canonical_certificate_quotient_dimension_le_packet_card
import Theorems.Thm_ConnesGreen_canonical_omitted_integral_rows_finite_modulo_gram_kernel
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability
theorem solution
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros) (δ : ℝ) (hδ : 0 < δ) :
    ∃ G : Finset CriticalZeros, G.card ≤ S.card ∧
      (∀ ρ ∈ G, ρ ∉ F) ∧
      ∀ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
        canonicalFiniteIntegralCertificate t S F δ *ᵥ c = 0 →
        ((∀ ρ ∈ G, canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) ↔
        ∀ ρ : CriticalZeros, ρ ∉ F → canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) := by
  obtain ⟨G, hcard, hG, hrows⟩ :=
    canonical_omitted_integral_rows_finite_modulo_gram_kernel t ht S F δ
  exact ⟨G, hcard.trans (canonical_certificate_quotient_dimension_le_packet_card t ht S F δ hδ),
    hG, hrows⟩
