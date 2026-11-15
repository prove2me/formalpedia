-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a379_masked_compensator_sum_split_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:56:29.311945+00:00
-- url     : https://prove2.me/submissions/334348af-06b0-4e09-805a-52e160a1ec17

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

theorem solution
    (S : Finset ℕ) (F L G : ℕ → ℝ)
    (A : ℕ → Prop) [DecidablePred A] :
    (∑ i ∈ S, F i) -
      (∑ i ∈ S, if A i then L i else 0) -
      (∑ i ∈ S, if A i then G i else 0) =
    (∑ i ∈ S, F i) -
      (∑ i ∈ S, if A i then L i + G i else 0) := by
  classical
  have hsum : (∑ i ∈ S, if A i then L i + G i else 0) =
      (∑ i ∈ S, if A i then L i else 0) +
      (∑ i ∈ S, if A i then G i else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ha : A i <;> simp [ha]
  rw [hsum]
  ring
