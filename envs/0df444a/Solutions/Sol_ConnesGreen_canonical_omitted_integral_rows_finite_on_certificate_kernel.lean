-- Prove2me | solution 1 for ConnesGreen.canonical_omitted_integral_rows_finite_on_certificate_kernel
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T17:30:44.150987+00:00
-- url     : https://prove2.me/submissions/1a1ff669-abd8-4dd2-bd7a-e74c723f77a1

import Definitions.Def_ConnesGreen_integral_sampling_row
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

import Theorems.Thm_WeilDefect_MarkerStability_finite_sampling_on_matrix_kernel
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability
theorem solution
    (t : ℝ) (S F : Finset CriticalZeros) (δ : ℝ) :
    ∃ G : Finset CriticalZeros, G.card ≤ Module.finrank ℂ
      (LinearMap.ker (canonicalFiniteIntegralCertificate t S F δ).mulVecLin) ∧
      (∀ ρ ∈ G, ρ ∉ F) ∧
      ∀ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
        canonicalFiniteIntegralCertificate t S F δ *ᵥ c = 0 →
        ((∀ ρ ∈ G, canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) ↔
        ∀ ρ : CriticalZeros, ρ ∉ F → canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) := by
  obtain ⟨G₀, hcard, hrows⟩ := finite_sampling_on_matrix_kernel
    (canonicalFiniteIntegralCertificate t S F δ)
    (fun ρ : {ρ : CriticalZeros // ρ ∉ F} => canonicalIntegralSamplingRow t S F ρ.1)
  refine ⟨G₀.image Subtype.val, ?_, ?_, ?_⟩
  · exact (Finset.card_image_le).trans (by simpa using hcard)
  · intro ρ hρ
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hρ
    exact σ.2
  · intro c hc
    constructor
    · intro h ρ hρ
      exact (hrows c hc).mp (fun σ hσ => h σ.1
        (Finset.mem_image.mpr ⟨σ, hσ, rfl⟩)) ⟨ρ, hρ⟩
    · intro h ρ hρ
      obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact h σ.1 σ.2
