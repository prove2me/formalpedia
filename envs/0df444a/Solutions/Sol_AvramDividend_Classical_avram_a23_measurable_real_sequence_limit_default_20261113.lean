-- Prove2me | solution 1 for AvramDividend.Classical.avram_a23_measurable_real_sequence_limit_default_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:17:12.678211+00:00
-- url     : https://prove2.me/submissions/43c7de17-0b3d-44a7-be6c-79780e48112b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

/-- The default-valued limit of countably many measurable real-valued functionals is measurable and coincides with every actual limit. -/
theorem solution
    {X : Type*} [MeasurableSpace X]
    (W : ℕ → X → ℝ) (hW : ∀ n, Measurable (W n)) :
    ∃ Wlim : X → ℝ,
      Measurable Wlim ∧
      ∀ x : X, ∀ r : ℝ,
        Tendsto (fun n : ℕ => W n x) atTop (𝓝 r) →
          Wlim x = r := by
  let Wlim : X → ℝ := fun x =>
    Filter.limUnder atTop (fun n : ℕ => W n x)
  have hStrong : StronglyMeasurable Wlim := by
    exact MeasureTheory.StronglyMeasurable.limUnder
      (l := atTop) (f := W) (fun n => (hW n).stronglyMeasurable)
  refine ⟨Wlim, hStrong.measurable, ?_⟩
  intro x r h
  exact h.limUnder_eq
