-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_finite_real_measures_eq_of_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:48:25.200557+00:00
-- url     : https://prove2.me/submissions/47604e03-87e6-4d0a-b763-40f0a09ac191

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

/-- Equality of finite measures follows from equal total mass and strict upper tails. -/
theorem solution
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hUniv : μ Set.univ = ν Set.univ)
    (hIoi : ∀ a : ℝ, μ (Set.Ioi a) = ν (Set.Ioi a)) :
    μ = ν := by
  apply Measure.ext_of_Iic
  intro a
  calc
    μ (Iic a) = μ Set.univ - μ (Ioi a) := by
      simpa only [compl_Ioi] using
        (measure_compl measurableSet_Ioi (measure_ne_top μ (Ioi a)))
    _ = ν Set.univ - ν (Ioi a) := by rw [hUniv, hIoi a]
    _ = ν (Iic a) := by
      simpa only [compl_Ioi] using
        (measure_compl measurableSet_Ioi (measure_ne_top ν (Ioi a))).symm
