-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_bounded_ae_limit_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T21:59:37.116098+00:00
-- url     : https://prove2.me/submissions/26e64e58-4803-418d-9141-5b0d52464444

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : ℕ → α → ℝ) (g : α → ℝ) (C : ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hbound : ∀ n t, ‖F n t‖ ≤ C)
    (hlim : ∀ᵐ t ∂μ, Tendsto (fun n => F n t) atTop (nhds (g t))) :
    Integrable g μ := by
  have hgm : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hF hlim
  apply (integrable_const C).mono' hgm
  filter_upwards [hlim] with t ht
  exact le_of_tendsto' ht.norm (fun n => hbound n t)
