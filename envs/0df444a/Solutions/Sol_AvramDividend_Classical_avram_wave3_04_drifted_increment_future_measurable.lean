-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_drifted_increment_future_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:51:22.909908+00:00
-- url     : https://prove2.me/submissions/a8d7c18b-3afe-4264-899f-7bbda8b77d8c

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- A drifted increment is measurable against the whole future increment path. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (U : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    MeasurableSpace.comap
      (fun ω => (U t ω - (t : ℝ)) - (U s ω - (s : ℝ)))
      inferInstance ≤
    MeasurableSpace.comap
      (fun ω (r : ℝ≥0) => U (s + r) ω - U s ω)
      inferInstance := by
  let g : (ℝ≥0 → ℝ) → ℝ :=
    fun p => p (t - s) - ((t : ℝ) - (s : ℝ))
  have hg : Measurable g :=
    (measurable_pi_apply (t - s)).sub_const _
  have hf :
      (fun ω => (U t ω - (t : ℝ)) - (U s ω - (s : ℝ))) =
      g ∘ (fun ω (r : ℝ≥0) => U (s + r) ω - U s ω) := by
    funext ω
    dsimp [g]
    rw [add_tsub_cancel_of_le hst]
    ring
  rw [hf]
  simpa only [MeasurableSpace.comap_comp] using
    (MeasurableSpace.comap_mono hg.comap_le :
      MeasurableSpace.comap
        (fun ω (r : ℝ≥0) => U (s + r) ω - U s ω)
        (MeasurableSpace.comap g inferInstance) ≤
      MeasurableSpace.comap
        (fun ω (r : ℝ≥0) => U (s + r) ω - U s ω)
        inferInstance)
