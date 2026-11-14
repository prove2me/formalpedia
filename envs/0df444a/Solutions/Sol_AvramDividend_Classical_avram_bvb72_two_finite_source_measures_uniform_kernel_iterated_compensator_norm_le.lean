-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb72_two_finite_source_measures_uniform_kernel_iterated_compensator_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:03:41.291895+00:00
-- url     : https://prove2.me/submissions/11f0c1cc-1cfc-40e1-a5c2-ab7b38d0fc31

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Set α) (hS : MeasurableSet S) (hμ : μ S < ⊤)
    (ν : Measure ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hν : ν B < ⊤)
    (f : α → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hKernel : ∀ t ∈ S, ∀ z ∈ B, |f t z| ≤ K) :
    ‖∫ t in S, ∫ z in B, f t z ∂ν ∂μ‖ ≤
      (K * (ν B).toReal) * (μ S).toReal := by
  have hInner : ∀ t ∈ S,
      ‖∫ z in B, f t z ∂ν‖ ≤ K * (ν B).toReal := by
    intro t ht
    apply norm_setIntegral_le_of_norm_le_const_ae' hν
    filter_upwards [] with z
    intro hz
    simpa only [Real.norm_eq_abs] using hKernel t ht z hz
  have hOuter :
      ‖∫ t in S, ∫ z in B, f t z ∂ν ∂μ‖ ≤
        (K * (ν B).toReal) * (μ S).toReal := by
    apply norm_setIntegral_le_of_norm_le_const_ae' hμ
    filter_upwards [] with t
    intro ht
    exact hInner t ht
  exact hOuter
