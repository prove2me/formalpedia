-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys109_finite_atomless_mark_neighbourhood_mass_tends_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:34:44.142269+00:00
-- url     : https://prove2.me/submissions/a357b163-cc23-42d7-b315-2a2897a35b8b

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- A finite jump-mark measure with no atom at a contact threshold
has vanishing mass in shrinking closed neighbourhoods of that mark. -/
theorem solution
    (μ : Measure ℝ)
    (hfinite : μ Set.univ < ⊤)
    (a : ℝ) (hatom : μ ({a} : Set ℝ) = 0) :
    Tendsto (fun δ : ℝ => μ (Icc (a - δ) (a + δ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  letI : IsFiniteMeasure μ := ⟨hfinite⟩
  simpa [hatom] using (tendsto_measure_Icc_nhdsWithin_right' μ a)
