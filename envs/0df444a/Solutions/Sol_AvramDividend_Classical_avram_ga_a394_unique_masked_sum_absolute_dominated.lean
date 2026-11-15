-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a394_unique_masked_sum_absolute_dominated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:52:38.154949+00:00
-- url     : https://prove2.me/submissions/52bdd2d8-2a2f-4407-a92b-bad674f93e32

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a392_unique_masked_sum_positive_dominated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

theorem solution
    (m : ℕ) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hUnique : ∀ i j, P i → P j → i = j)
    (hBound : ∀ i < m, P i → |f i| ≤ B) :
    |∑ i ∈ Finset.range m, if P i then f i else 0| ≤ B := by
  classical
  let S : ℝ := ∑ i ∈ Finset.range m, if P i then f i else 0
  have hp : max S 0 ≤ B := by
    exact avram_ga_a392_unique_masked_sum_positive_dominated
      m P f B hB hUnique (by
        intro i hi hpi
        exact max_le (le_trans (le_abs_self (f i)) (hBound i hi hpi)) hB)
  have hn : max (-S) 0 ≤ B := by
    have hneg := avram_ga_a392_unique_masked_sum_positive_dominated
      m P (fun i => -f i) B hB hUnique (by
        intro i hi hpi
        exact max_le
          (le_trans (neg_le_abs (f i)) (hBound i hi hpi)) hB)
    have heq : (∑ i ∈ Finset.range m, if P i then -f i else 0) = -S := by
      dsimp [S]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hpi : P i <;> simp [hpi]
    simpa only [heq] using hneg
  apply abs_le.mpr
  constructor
  · have hh : -S ≤ B := (le_max_left (-S) 0).trans hn
    linarith
  · exact (le_max_left S 0).trans hp
