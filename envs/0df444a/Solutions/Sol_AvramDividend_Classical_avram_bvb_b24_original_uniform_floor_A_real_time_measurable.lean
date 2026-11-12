-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b24_original_uniform_floor_A_real_time_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:34:50.445499+00:00
-- url     : https://prove2.me/submissions/45b6fab4-29d3-4f29-b5ae-4bcd54607d4b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- The genuine truncated original uniform-floor A coefficient is Borel measurable in real time. -/
theorem solution
    (T : ℝ) (n : ℕ) (c : ℕ → ℝ) :
    Measurable (fun t : ℝ =>
      if 0 ≤ t ∧
         t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2) then
        c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0) := by
  have hc : Measurable c := measurable_of_countable c
  have hfloor : Measurable
      (fun t : ℝ => ⌊(t / T) * ((n : ℝ) + 2)⌋₊) :=
    ((measurable_id.div_const T).mul_const ((n : ℝ) + 2)).nat_floor
  have hmask : MeasurableSet
      {t : ℝ | 0 ≤ t ∧
         t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)} :=
    measurableSet_Ici.inter measurableSet_Iio
  exact (hc.comp hfloor).ite hmask measurable_const
