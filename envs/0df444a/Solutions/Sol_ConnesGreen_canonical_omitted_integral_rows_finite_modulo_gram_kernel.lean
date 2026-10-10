-- Prove2me | solution 1 for ConnesGreen.canonical_omitted_integral_rows_finite_modulo_gram_kernel
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T18:21:05.386984+00:00
-- url     : https://prove2.me/submissions/34896190-e16e-4902-a6e0-a462b2e535db

import Definitions.Def_ConnesGreen_integral_sampling_row
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

import Theorems.Thm_WeilDefect_MarkerStability_finite_sampling_on_matrix_kernel_modulo
import Theorems.Thm_ConnesGreen_canonical_gram_null_sampling_custody
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability
theorem solution
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros) (δ : ℝ) :
    ∃ G : Finset CriticalZeros, G.card ≤ Module.finrank ℂ
      (LinearMap.ker (canonicalFiniteIntegralCertificate t S F δ).mulVecLin) -
      Module.finrank ℂ (LinearMap.ker (canonicalFiniteColumnKernel t S F).mulVecLin) ∧
      (∀ ρ ∈ G, ρ ∉ F) ∧
      ∀ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
        canonicalFiniteIntegralCertificate t S F δ *ᵥ c = 0 →
        ((∀ ρ ∈ G, canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) ↔
        ∀ ρ : CriticalZeros, ρ ∉ F → canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) := by
  obtain ⟨hHK, hz⟩ := canonical_gram_null_sampling_custody t ht S F δ
  obtain ⟨G₀, hcard, hrows⟩ := finite_sampling_on_matrix_kernel_modulo
    (canonicalFiniteIntegralCertificate t S F δ) (canonicalFiniteColumnKernel t S F)
    (fun ρ : {ρ : CriticalZeros // ρ ∉ F} => canonicalIntegralSamplingRow t S F ρ.1) hHK (fun ρ => hz ρ.1)
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
