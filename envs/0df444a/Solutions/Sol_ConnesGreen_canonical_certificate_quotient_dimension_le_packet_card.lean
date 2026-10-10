-- Prove2me | solution 1 for ConnesGreen.canonical_certificate_quotient_dimension_le_packet_card
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T20:08:32.498772+00:00
-- url     : https://prove2.me/submissions/cb579f74-0fa3-4f4e-9a33-a4349b70bc49

import Definitions.Def_ConnesGreen_integral_sampling_row
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

import Theorems.Thm_WeilDefect_MarkerStability_submodule_dimension_difference_le_analysis_card
import Theorems.Thm_ConnesGreen_canonical_gram_null_sampling_custody
import Theorems.Thm_ConnesGreen_canonical_negative_coordinates_detect_gram_null
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability
theorem solution
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros) (δ : ℝ) (hδ : 0 < δ) :
    Module.finrank ℂ (LinearMap.ker (canonicalFiniteIntegralCertificate t S F δ).mulVecLin) -
      Module.finrank ℂ (LinearMap.ker (canonicalFiniteColumnKernel t S F).mulVecLin) ≤ S.card := by
  let L : (({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ) →ₗ[ℂ]
      ({ρ : CriticalZeros // ρ ∈ S} → ℂ) :=
    LinearMap.pi (fun ρ => (LinearMap.proj (Sum.inr ρ)).comp
      (canonicalFiniteColumnKernel t S F).mulVecLin)
  obtain ⟨hHK, _⟩ := canonical_gram_null_sampling_custody t ht S F δ
  have hh := submodule_dimension_difference_le_analysis_card
    (LinearMap.ker (canonicalFiniteIntegralCertificate t S F δ).mulVecLin)
    (LinearMap.ker (canonicalFiniteColumnKernel t S F).mulVecLin) hHK L ?_
  · simpa only [Fintype.card_coe] using hh
  · intro c hc
    constructor
    · intro hn
      apply (canonical_negative_coordinates_detect_gram_null t ht S F δ hδ c hc).mp
      intro ρ
      exact congrFun hn ρ
    · intro hn
      change canonicalFiniteColumnKernel t S F *ᵥ c = 0 at hn
      funext ρ
      change (canonicalFiniteColumnKernel t S F *ᵥ c) (Sum.inr ρ) = 0
      rw [hn]
      rfl
