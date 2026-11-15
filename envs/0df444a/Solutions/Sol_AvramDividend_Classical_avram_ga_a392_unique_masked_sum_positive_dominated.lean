-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a392_unique_masked_sum_positive_dominated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:37:59.056631+00:00
-- url     : https://prove2.me/submissions/38f6bd5f-504c-41cf-9b95-b4a2517aabf3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a381_unique_masked_sum_pospart_v2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

theorem solution
    (m : ℕ) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hUnique : ∀ i j, P i → P j → i = j)
    (hBound : ∀ i < m, P i → max (f i) 0 ≤ B) :
    max (∑ i ∈ Finset.range m, if P i then f i else 0) 0 ≤ B := by
  classical
  rw [avram_ga_a381_unique_masked_sum_pospart_v2 m P f hUnique]
  have hmain : ∀ (k : ℕ), (∀ i < k, P i → max (f i) 0 ≤ B) →
      (∑ i ∈ Finset.range k, if P i then max (f i) 0 else 0) ≤ B := by
    intro k
    induction k with
    | zero => intro hb; simpa using hB
    | succ k ih =>
      intro hb
      by_cases hp : P k
      · have hother : ∀ i ∈ Finset.range k, ¬ P i := by
          intro i hi hpi
          have heq := hUnique i k hpi hp
          exact (Nat.ne_of_lt (Finset.mem_range.mp hi)) heq
        have hz : (∑ i ∈ Finset.range k,
            if P i then max (f i) 0 else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          simp [hother i hi]
        rw [Finset.sum_range_succ, hz]
        simpa [hp] using hb k (Nat.lt_succ_self k) hp
      · rw [Finset.sum_range_succ]
        simp only [if_neg hp, add_zero]
        exact ih (fun i hi hpi => hb i (hi.trans (Nat.lt_succ_self k)) hpi)
  exact hmain m hBound
