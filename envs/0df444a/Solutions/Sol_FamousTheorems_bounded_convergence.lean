-- Prove2me | solution 1 for FamousTheorems.bounded_convergence
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T17:51:32.438649+00:00
-- url     : https://prove2.me/submissions/a2d28755-713d-49e1-882f-cbb1579af5c4

import Mathlib

open MeasureTheory

theorem solution {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {F : ℕ → α → ℝ} {f : α → ℝ} (C : ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ C)
    (h_lim : ∀ᵐ a ∂μ, Filter.Tendsto (fun n => F n a) Filter.atTop (nhds (f a))) :
    Filter.Tendsto (fun n => ∫ a, F n a ∂μ) Filter.atTop (nhds (∫ a, f a ∂μ)) :=
  tendsto_integral_of_dominated_convergence (fun _ => C) hF (integrable_const C) h_bound h_lim
