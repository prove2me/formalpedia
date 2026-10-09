-- Prove2me | solution 1 for ConnesGreen.canonical_picard_half_iff_unrestricted_finite_certificates
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T00:22:37.799851+00:00
-- url     : https://prove2.me/submissions/d02b7ce8-f1f4-4285-acd0-d237f0718f85

import Theorems.Thm_ConnesGreen_canonical_finite_certificate_complete_cutoff
import Theorems.Thm_ConnesGreen_canonical_picard_half_iff_finite_selected_certificates
import Definitions.Def_ConnesGreen_finite_selected_correction
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Complex ConnesRZ ConnesRZFrontier ConnesGreen
open WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section

open Filter
theorem solution
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S) ↔
    ∀ δ : ℝ, 0 < δ → ∃ F : Finset CriticalZeros,
      0 ≤ canonicalFiniteSelectedCorrection t ht S F δ := by
  rw [canonical_picard_half_iff_finite_selected_certificates]
  constructor
  · intro h δ hδ
    obtain ⟨F, _, _, _, hF⟩ := h δ hδ
    exact ⟨F, hF⟩
  · intro h δ hδ
    obtain ⟨F, hF⟩ := h δ hδ
    obtain ⟨G, _, hSG, hclosed, htail, hG⟩ :=
      canonical_finite_certificate_complete_cutoff t ht S F δ δ hδ hδ hF
    exact ⟨G, hSG, hclosed, htail, hG⟩
