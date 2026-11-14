-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_integrable_original_mark_kernel_eventual_mask_integral_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:17.394569+00:00
-- url     : https://prove2.me/submissions/475881c0-8263-4dcb-9b92-15910db16e2e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {α : Type*} [m : MeasurableSpace α] (μ : Measure α)
    (H : α → ℝ) (hH : Integrable H μ)
    (s : ℕ → Set α) (hs : ∀ n, MeasurableSet (s n))
    (hExhaust : ∀ᵐ p ∂μ, ∀ᶠ n : ℕ in atTop, p ∈ s n) :
    Tendsto (fun n : ℕ => ∫ p, if p ∈ s n then H p else 0 ∂μ)
      atTop (𝓝 (∫ p, H p ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence
    (fun p => ‖H p‖) ?_ hH.norm ?_ ?_
  · intro n
    exact (hH.indicator (hs n)).aestronglyMeasurable
  · intro n
    filter_upwards [] with p
    by_cases hp : p ∈ s n
    · simp [hp]
    · simp [hp]
  · filter_upwards [hExhaust] with p hp
    have hEq : (fun _ : ℕ => H p) =ᶠ[atTop]
        (fun n : ℕ => if p ∈ s n then H p else 0) :=
      hp.mono (fun n hn => by simp [hn])
    exact tendsto_const_nhds.congr' hEq
