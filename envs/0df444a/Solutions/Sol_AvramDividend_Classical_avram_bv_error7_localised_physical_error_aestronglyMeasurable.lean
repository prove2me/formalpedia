-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_localised_physical_error_aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:42:19.787587+00:00
-- url     : https://prove2.me/submissions/213923c6-f7f8-44c5-98f6-b161f2844ca2

import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped Classical
noncomputable section

/-- The original stopped-grid residual remains a.e. strongly measurable
after restriction to any measurable interior localisation event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
    (s : Set Ω) (hs : MeasurableSet s)
    (Err : ℕ → Ω → ℝ)
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P) :
    ∀ m, AEStronglyMeasurable
      (fun ω => if ω ∈ s then Err m ω else 0) P := by
  intro m
  change AEStronglyMeasurable (s.indicator (Err m)) P
  exact (hErrMeas m).indicator hs
