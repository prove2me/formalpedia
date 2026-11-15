-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_positive_probability_witness_refutes_ae_cash_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:52:38.97985+00:00
-- url     : https://prove2.me/submissions/05a266ab-1852-48af-aeb0-3a271c2942f8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : Set Ω) (hE : 0 < P E)
    (F : Ω → ℝ) (hWitness : ∀ ω ∈ E, 0 < F ω) :
    ¬ (∀ᵐ ω ∂P, F ω ≤ 0) := by
  intro hUpper
  have hZero : P {ω | ¬ F ω ≤ 0} = 0 := (ae_iff).mp hUpper
  have hSubset : E ⊆ {ω | ¬ F ω ≤ 0} := by
    intro ω hMem
    exact not_le_of_gt (hWitness ω hMem)
  have hMono : P E ≤ P {ω | ¬ F ω ≤ 0} := measure_mono hSubset
  rw [hZero] at hMono
  exact (not_le_of_gt hE) hMono
