-- Prove2me | solution 1 for AvramDividend.Classical.measure_restrict_iUnion_eq_of_mono_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:18:16.152132+00:00
-- url     : https://prove2.me/submissions/88f787bf-462f-4521-a8f1-e381dbd5a58b

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (μ ν : Measure ℝ) (s : ℕ → Set ℝ)
    (hmono : Monotone s)
    (heq : ∀ n, μ.restrict (s n) = ν.restrict (s n)) :
    μ.restrict (⋃ n, s n) = ν.restrict (⋃ n, s n) := by
  have hd : Directed (· ⊆ ·) s := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · exact hmono (le_max_left i j)
    · exact hmono (le_max_right i j)
  apply Measure.ext
  intro t ht
  rw [μ.restrict_iUnion_apply_eq_iSup hd ht,
      ν.restrict_iUnion_apply_eq_iSup hd ht]
  apply iSup_congr
  intro n
  exact congrArg (fun η : Measure ℝ => η t) (heq n)
