-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva20_paired_dominated_integral_difference_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:26:49.576235+00:00
-- url     : https://prove2.me/submissions/57f5f1bc-fe63-4f1d-9894-fe89e230c1b6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped Topology
noncomputable section

/-- Paired dominated integral sequences with a common limit have vanishing difference. -/
theorem solution
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsFiniteMeasure μ] (B : ℝ)
    (F G : ℕ → α → ℝ) (f : α → ℝ)
    (hFmeas : ∀ n, MeasureTheory.AEStronglyMeasurable (F n) μ)
    (hGmeas : ∀ n, MeasureTheory.AEStronglyMeasurable (G n) μ)
    (hFbound : ∀ n, ∀ᵐ t ∂μ, ‖F n t‖ ≤ B)
    (hGbound : ∀ n, ∀ᵐ t ∂μ, ‖G n t‖ ≤ B)
    (hFlim : ∀ᵐ t ∂μ, Filter.Tendsto
      (fun n : ℕ => F n t) Filter.atTop (nhds (f t)))
    (hGlim : ∀ᵐ t ∂μ, Filter.Tendsto
      (fun n : ℕ => G n t) Filter.atTop (nhds (f t))) :
    Filter.Tendsto
      (fun n : ℕ => (∫ t, F n t ∂μ) - (∫ t, G n t ∂μ))
      Filter.atTop (nhds (0 : ℝ)) := by
  have hInt : Integrable (fun _ : α => B) μ := integrable_const _
  have hFt : Tendsto (fun n => ∫ t, F n t ∂μ) atTop
      (𝓝 (∫ t, f t ∂μ)) :=
    tendsto_integral_of_dominated_convergence
      (fun _ : α => B) hFmeas hInt hFbound hFlim
  have hGt : Tendsto (fun n => ∫ t, G n t ∂μ) atTop
      (𝓝 (∫ t, f t ∂μ)) :=
    tendsto_integral_of_dominated_convergence
      (fun _ : α => B) hGmeas hInt hGbound hGlim
  simpa only [sub_self] using hFt.sub hGt
