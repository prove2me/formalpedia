-- Prove2me | solution 1 for AvramDividend.Classical.avram_b29_centered_gaussian_coordinate_product_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:04:02.077602+00:00
-- url     : https://prove2.me/submissions/697ba12c-5f2a-4f5d-b918-fc95a399b379

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

theorem solution
    {ΩB ΩN : Type*} [mB : MeasurableSpace ΩB]
    [mN : MeasurableSpace ΩN]
    (μ : Measure ΩB) (ν : Measure ΩN)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : ℕ → ΩB → ℝ)
    (hIntegrable : ∀ k, Integrable (H k) μ)
    (hMean : ∀ k, (∫ ω, H k ω ∂μ) = 0) :
    (∀ k, Integrable (fun p : ΩB × ΩN => H k p.1) (μ.prod ν)) ∧
    (∀ k, (∫ p : ΩB × ΩN, H k p.1 ∂(μ.prod ν)) = 0) := by
  constructor
  · intro k
    exact (hIntegrable k).comp_fst ν
  · intro k
    rw [integral_fun_fst (μ := μ) (ν := ν) (H k), hMean k]
    simp
