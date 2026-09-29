-- Prove2me | solution 1 for FamousTheorems.riesz_markov_kakutani
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:20:40.167912+00:00
-- url     : https://prove2.me/submissions/354d0b12-dc7c-4bd2-add8-29c3c4b1e5fc

import Mathlib

theorem solution {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (Λ : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ) :
    ∃ μ : MeasureTheory.Measure X, μ.Regular ∧
      ∀ f : CompactlySupportedContinuousMap X ℝ, ∫ x, f x ∂μ = Λ f :=
  ⟨RealRMK.rieszMeasure Λ, inferInstance, fun f => RealRMK.integral_rieszMeasure Λ f⟩
