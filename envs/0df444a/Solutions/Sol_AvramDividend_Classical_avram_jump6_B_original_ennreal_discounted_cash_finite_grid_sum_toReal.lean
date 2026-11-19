-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_ennreal_discounted_cash_finite_grid_sum_toReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:40:06.269278+00:00
-- url     : https://prove2.me/submissions/4bb81844-40ae-45f3-ab0b-e42278345a1b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

theorem solution
    {ι : Type*} (S : Finset ι) (E H : ι → ℝ)
    (hE : ∀ i ∈ S, 0 ≤ E i) (hH : ∀ i ∈ S, 0 ≤ H i) :
    (∑ i ∈ S, ENNReal.ofReal (E i) * ENNReal.ofReal (H i)).toReal =
      ∑ i ∈ S, E i * H i := by
  have hEH : ∀ i ∈ S, 0 ≤ E i * H i := by
    intro i hi
    exact mul_nonneg (hE i hi) (hH i hi)
  have hterms : ∀ i ∈ S,
      ENNReal.ofReal (E i) * ENNReal.ofReal (H i) =
        ENNReal.ofReal (E i * H i) := by
    intro i hi
    exact (ENNReal.ofReal_mul (hE i hi)).symm
  calc
    (∑ i ∈ S, ENNReal.ofReal (E i) * ENNReal.ofReal (H i)).toReal =
        (∑ i ∈ S, ENNReal.ofReal (E i * H i)).toReal := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          exact hterms i hi
    _ = (ENNReal.ofReal (∑ i ∈ S, E i * H i)).toReal := by
          rw [ENNReal.ofReal_sum_of_nonneg hEH]
    _ = ∑ i ∈ S, E i * H i := by
          rw [ENNReal.toReal_ofReal (Finset.sum_nonneg hEH)]
