-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a381_unique_masked_sum_pospart_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:55:45.618189+00:00
-- url     : https://prove2.me/submissions/8273898f-2858-4cc3-a43d-a882dbcf2248

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

theorem solution
    (m : ℕ) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℝ)
    (hUnique : ∀ i j, P i → P j → i = j) :
    max (∑ i ∈ Finset.range m, if P i then f i else 0) 0 =
      ∑ i ∈ Finset.range m, if P i then max (f i) 0 else 0 := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    by_cases hp : P m
    · have hother : ∀ i ∈ Finset.range m, ¬ P i := by
        intro i hi hpi
        have heq : i = m := hUnique i m hpi hp
        exact (Nat.ne_of_lt (Finset.mem_range.mp hi)) heq
      have hsum (g : ℕ → ℝ) :
          (∑ i ∈ Finset.range m, if P i then g i else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp [hother i hi]
      simp only [Finset.sum_range_succ]
      rw [hsum f, hsum (fun i => max (f i) 0)]
      simp [hp]
    · simp only [Finset.sum_range_succ]
      simp [hp, ih]
