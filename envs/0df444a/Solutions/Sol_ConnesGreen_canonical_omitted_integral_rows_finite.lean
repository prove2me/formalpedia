-- Prove2me | solution 1 for ConnesGreen.canonical_omitted_integral_rows_finite
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T17:08:15.364871+00:00
-- url     : https://prove2.me/submissions/f8e8b024-cc52-4d8b-946e-48b98847c0bc

import Definitions.Def_ConnesGreen_integral_sampling_row

import Theorems.Thm_WeilDefect_MarkerStability_finite_sampling_rows_determine_all
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability
theorem solution
    (t : ℝ) (S F : Finset CriticalZeros) :
    ∃ G : Finset CriticalZeros, G.card ≤ F.card + S.card ∧
      (∀ ρ ∈ G, ρ ∉ F) ∧
      ∀ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
        (∀ ρ ∈ G, canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) ↔
        ∀ ρ : CriticalZeros, ρ ∉ F → canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0 := by
  obtain ⟨G₀, hcard, hrows⟩ := finite_sampling_rows_determine_all
    (fun ρ : {ρ : CriticalZeros // ρ ∉ F} => canonicalIntegralSamplingRow t S F ρ.1)
  refine ⟨G₀.image Subtype.val, ?_, ?_, ?_⟩
  · exact (Finset.card_image_le).trans (by simpa using hcard)
  · intro ρ hρ
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hρ
    exact σ.2
  · intro c
    constructor
    · intro h ρ hρ
      exact (hrows c).mp (fun σ hσ => h σ.1
        (Finset.mem_image.mpr ⟨σ, hσ, rfl⟩)) ⟨ρ, hρ⟩
    · intro h ρ hρ
      obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact h σ.1 σ.2
