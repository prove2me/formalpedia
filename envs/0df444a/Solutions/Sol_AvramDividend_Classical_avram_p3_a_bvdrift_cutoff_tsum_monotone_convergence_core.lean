-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_cutoff_tsum_monotone_convergence_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:26:30.640398+00:00
-- url     : https://prove2.me/submissions/becf9de9-3903-4b39-bf33-a32beaeca1da

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- An antitone size cutoff cofinal below every positive jump magnitude
recovers the full ENNReal total through monotone cutoff sums. -/
theorem solution
    {α : Type*} (f : α → ℝ≥0∞)
    (ε : ℕ → ℝ≥0∞) (hε : Antitone ε)
    (hCover : ∀ a, 0 < f a → ∃ n : ℕ, ε n < f a) :
    (⨆ n : ℕ, ∑' a : α, if ε n < f a then f a else 0) =
      ∑' a : α, f a := by
  classical
  have hs : ∀ s : Finset α,
      ∃ n : ℕ, ∀ a ∈ s, 0 < f a → ε n < f a := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨0, by simp⟩
    | @insert a s ha ih =>
        obtain ⟨n, hn⟩ := ih
        by_cases hp : 0 < f a
        · obtain ⟨m, hm⟩ := hCover a hp
          refine ⟨max m n, ?_⟩
          intro b hb hbpos
          rcases Finset.mem_insert.mp hb with rfl | hbs
          · exact lt_of_le_of_lt (hε (Nat.le_max_left m n)) hm
          · exact lt_of_le_of_lt (hε (Nat.le_max_right m n)) (hn b hbs hbpos)
        · refine ⟨n, ?_⟩
          intro b hb hbpos
          rcases Finset.mem_insert.mp hb with rfl | hbs
          · exact False.elim (hp hbpos)
          · exact hn b hbs hbpos
  apply le_antisymm
  · refine iSup_le fun n => ENNReal.tsum_le_tsum (fun a => ?_)
    by_cases hp : ε n < f a
    · simp [hp]
    · simp [hp]
  · rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    obtain ⟨n, hn⟩ := hs s
    calc
      (∑ a ∈ s, f a) =
          ∑ a ∈ s, (if ε n < f a then f a else 0) := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases hp : 0 < f a
            · simp [hn a ha hp]
            · have hz : f a = 0 := le_antisymm (le_of_not_gt hp) bot_le
              simp [hz]
      _ ≤ ∑' a : α, if ε n < f a then f a else 0 :=
        ENNReal.sum_le_tsum s
      _ ≤ ⨆ n : ℕ, ∑' a : α, if ε n < f a then f a else 0 :=
        le_iSup_of_le n le_rfl