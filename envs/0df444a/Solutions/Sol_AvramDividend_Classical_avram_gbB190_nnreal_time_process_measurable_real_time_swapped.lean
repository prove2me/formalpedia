-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB190_nnreal_time_process_measurable_real_time_swapped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T19:14:25.318617+00:00
-- url     : https://prove2.me/submissions/a1980d7d-8ed9-4af4-8aaf-956e52b2a36d

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (f : ℝ≥0 → Ω → ℝ)
    (hf : Measurable (fun z : ℝ≥0 × Ω => f z.1 z.2)) :
    Measurable (fun z : Ω × ℝ =>
      f (Real.toNNReal z.2) z.1) := by
  exact hf.comp
    ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk
      measurable_fst)
