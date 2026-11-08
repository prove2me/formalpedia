-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux20_monotone_finite_mark_sum_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:50:39.210878+00:00
-- url     : https://prove2.me/submissions/7b8a5ea3-bee5-41d3-89ca-b038fe12a1b4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-! Increasing finite marked sums commute with a countable supremum. -/
theorem solution
    {α : Type*} (S : Finset α) (f : ℕ → α → ℝ≥0∞)
    (hf : ∀ a, Monotone (fun n : ℕ => f n a)) :
    (⨆ n : ℕ, ∑ a ∈ S, f n a) =
      ∑ a ∈ S, (⨆ n : ℕ, f n a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hm : Monotone (fun n : ℕ => ∑ b ∈ S, f n b) := by
      intro i j hij
      exact Finset.sum_le_sum (fun b hb => hf b hij)
    have hdir : ∀ i j : ℕ, ∃ k : ℕ,
        f i a + (∑ b ∈ S, f j b) ≤
          f k a + (∑ b ∈ S, f k b) := by
      intro i j
      refine ⟨max i j, ?_⟩
      exact add_le_add (hf a (le_max_left i j))
        (hm (le_max_right i j))
    simp only [Finset.sum_insert ha]
    calc
      (⨆ n : ℕ, f n a + (∑ b ∈ S, f n b)) =
          (⨆ n : ℕ, f n a) +
            (⨆ n : ℕ, ∑ b ∈ S, f n b) :=
        (ENNReal.iSup_add_iSup hdir).symm
      _ = (⨆ n : ℕ, f n a) +
            (∑ b ∈ S, (⨆ n : ℕ, f n b)) := by rw [ih]
