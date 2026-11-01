-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_marked_value_increment_measurable_of_process_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:34:28.178876+00:00
-- url     : https://prove2.me/submissions/421ba260-7f4e-4e62-adfd-df86cebad578

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal Classical
noncomputable section

/-- Measurable marked jump increments for a pre-jump process in any σ-algebra. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (m : MeasurableSpace (ℝ≥0 × Ω))
    (U : ℝ≥0 × Ω → ℝ)
    (hU : Measurable[m] U)
    (w : ℝ → ℝ) (hw : Measurable w) :
    Measurable[m.prod inferInstance]
      (fun z : (ℝ≥0 × Ω) × ℝ =>
        w (U z.1 + z.2) - w (U z.1)) := by
  have hpre : Measurable[m.prod (inferInstance : MeasurableSpace ℝ)]
      (fun z : (ℝ≥0 × Ω) × ℝ => U z.1) :=
    hU.comp measurable_fst
  have hmark : Measurable[m.prod (inferInstance : MeasurableSpace ℝ)]
      (fun z : (ℝ≥0 × Ω) × ℝ => z.2) := measurable_snd
  exact (hw.comp (hpre.add hmark)).sub (hw.comp hpre)
