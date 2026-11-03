-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_borel_marked_grid_count_second_moment_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:59:30.100467+00:00
-- url     : https://prove2.me/submissions/28be161b-3552-4f31-9ab2-c7dc62f342c1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_count_exact_second_moment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- Quadratic control of the original marked-increment grid occupancy count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, (∑ i ∈ Finset.range n,
      ({v : Ω | X.X (t (i + 1)) v - X.X (t i) v ∈ B}).indicator
        (fun _ => (1 : ℝ≥0∞)) ω) ^ 2 ∂P) ≤
    (∑ i ∈ Finset.range n,
      P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}) +
    (∑ i ∈ Finset.range n,
      P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}) ^ 2 := by
  classical
  let S : Finset ℕ := Finset.range n
  let p : ℕ → ℝ≥0∞ := fun i =>
    P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}
  have hSecond :=
    avram_wave6_01_original_borel_marked_grid_count_exact_second_moment
      X t ht n B hB
  rw [hSecond]
  change (∑ i ∈ S, ∑ j ∈ S,
    if i = j then p i else p i * p j) ≤
      (∑ i ∈ S, p i) + (∑ i ∈ S, p i) ^ 2
  have hRow (i : ℕ) (hi : i ∈ S) :
      (∑ j ∈ S, if i = j then p i else p i * p j) ≤
        p i + ∑ j ∈ S, p i * p j := by
    calc
      (∑ j ∈ S, if i = j then p i else p i * p j) ≤
          ∑ j ∈ S, ((if i = j then p i else 0) + p i * p j) := by
            apply Finset.sum_le_sum
            intro j hj
            by_cases hij : i = j
            · simp only [if_pos hij]
              exact le_add_right le_rfl
            · simp [hij]
      _ = (∑ j ∈ S, if i = j then p i else 0) +
            ∑ j ∈ S, p i * p j := by
              rw [Finset.sum_add_distrib]
      _ = p i + ∑ j ∈ S, p i * p j := by
            simp [Finset.sum_ite_eq, hi]
  calc
    (∑ i ∈ S, ∑ j ∈ S,
      if i = j then p i else p i * p j) ≤
      ∑ i ∈ S, (p i + ∑ j ∈ S, p i * p j) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hRow i hi
    _ = (∑ i ∈ S, p i) +
      ∑ i ∈ S, ∑ j ∈ S, p i * p j := by
        rw [Finset.sum_add_distrib]
    _ = (∑ i ∈ S, p i) + (∑ i ∈ S, p i) ^ 2 := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
