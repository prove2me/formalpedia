-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_signed_grid_measurability_from_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:31:36.714678+00:00
-- url     : https://prove2.me/submissions/f9704685-86d9-4c9d-95a3-7b1cf99efc70

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal BigOperators

/-! Measurability of every finite signed grid sum follows from path-coordinate measurability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ)
    (hXm : ∀ t : ℝ≥0, Measurable (X t))
    (g : ℝ → ℝ) (hgm : Measurable g)
    (h : ℕ → ℝ) :
    ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => ∑ i ∈ Finset.range (n + 1),
        g (X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (h n)) ω -
           X ((i : ℝ≥0) * Real.toNNReal (h n)) ω)) P := by
  classical
  intro n
  have hsum : Measurable (fun ω => ∑ i ∈ Finset.range (n + 1),
      g (X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (h n)) ω -
         X ((i : ℝ≥0) * Real.toNNReal (h n)) ω)) := by
    apply Finset.measurable_sum
    intro i hi
    exact hgm.comp ((hXm _).sub (hXm _))
  exact hsum.aestronglyMeasurable
