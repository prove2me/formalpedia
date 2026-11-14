-- Prove2me | solution 1 for AvramDividend.Classical.avram_b77_original_true_stop_min_grid_stopping_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:59:20.668503+00:00
-- url     : https://prove2.me/submissions/afe58d62-a32c-4de7-a7e9-bf7d8dbbdd9b

import Mathlib.Probability.Process.Stopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

/-- Stopping every deterministic mesh time at the actual physical clock preserves stopping times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (κ : Ω → ℝ≥0)
    (hκstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (κ ω : WithTop ℝ≥0)))
    (u : ℕ → ℝ≥0) :
    ∀ i : ℕ, IsStoppingTime 𝓕.rightCont
      (fun ω => ((min (u i) (κ ω) : ℝ≥0) : WithTop ℝ≥0)) := by
  intro i
  have h := hκstop.min_const (u i)
  simpa only [WithTop.coe_min, min_comm] using h
