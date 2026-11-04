-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_finite_simple_centering_of_cell_compensation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:13:11.421206+00:00
-- url     : https://prove2.me/submissions/a2464c71-b93d-4561-8684-fb08d52cfe1a

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- Signed finite predictable-simple compensation follows from integrable
cellwise compensation. The cell means remain explicit source hypotheses. -/
theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Finset ι) (J C : ι → Ω → ℝ) (a : ι → ℝ)
    (hJI : ∀ i ∈ S, Integrable (J i) P)
    (hCI : ∀ i ∈ S, Integrable (C i) P)
    (hCells : ∀ i ∈ S, (∫ ω, J i ω ∂P) = (∫ ω, C i ω ∂P)) :
    Integrable (fun ω => ∑ i ∈ S, a i * (J i ω - C i ω)) P ∧
    (∫ ω, ∑ i ∈ S, a i * (J i ω - C i ω) ∂P) = 0 := by
  have hTerm : ∀ i ∈ S,
      Integrable (fun ω => a i * (J i ω - C i ω)) P := by
    intro i hi
    exact ((hJI i hi).sub (hCI i hi)).const_mul (a i)
  constructor
  · exact integrable_finset_sum S hTerm
  · rw [integral_finset_sum S hTerm]
    apply Finset.sum_eq_zero
    intro i hi
    rw [integral_const_mul, integral_sub (hJI i hi) (hCI i hi)]
    rw [hCells i hi]
    simp
