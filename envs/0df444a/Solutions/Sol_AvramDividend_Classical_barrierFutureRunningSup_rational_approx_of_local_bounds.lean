-- Prove2me | solution 1 for AvramDividend.Classical.barrierFutureRunningSup_rational_approx_of_local_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:14:35.973576+00:00
-- url     : https://prove2.me/submissions/a862b0ce-86eb-49b4-af29-97b5af5d67b8

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

lemma t10aux (a b : ℝ) (ha : 0 ≤ a) (h : a < b) :
    ∃ r : ℚ≥0, a < ((r : ℝ≥0) : ℝ) ∧ ((r : ℝ≥0) : ℝ) < b := by
  obtain ⟨q, h1, h2⟩ := exists_rat_btwn h
  have hq : (0:ℚ) ≤ q := by exact_mod_cast (ha.trans h1.le)
  refine ⟨⟨q, hq⟩, ?_, ?_⟩ <;> simpa using ‹_›

theorem solution
    (f : ℝ≥0 → ℝ) (t : ℝ≥0) (hf0 : f 0 = 0)
    (hRight : ∀ s : ℝ≥0, s < t → ∀ c : ℝ, c < f s →
      ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ≥0,
        s < r → (r : ℝ) - (s : ℝ) < ε → c < f r)
    (hLeft : 0 < t → ∀ c : ℝ, c < f t →
      ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ≥0,
        r < t → (t : ℝ) - (r : ℝ) < ε → c < f r) :
    ∀ s : Icc (0 : ℝ≥0) t, ∀ c : ℝ, c < max 0 (f s) →
      ∃ r : ℚ≥0, (r : ℝ≥0) ≤ t ∧ c < max 0 (f r) := by
  rintro ⟨s, hs0, hst⟩ c hc
  by_cases hc0 : c < 0
  · exact ⟨0, by simp, lt_max_of_lt_left (by simpa using hc0)⟩
  have hcs : c < f s := by
    rcases lt_max_iff.mp hc with h | h
    · exact absurd h hc0
    · exact h
  rcases hst.lt_or_eq with hlt | heq
  · obtain ⟨ε, hε, H⟩ := hRight s hlt c hcs
    obtain ⟨r, h1, h2⟩ := t10aux (s : ℝ) (min (t : ℝ) (s + ε)) s.2
      (lt_min (by exact_mod_cast hlt) (by linarith))
    refine ⟨r, ?_, lt_max_of_lt_right (H _ ?_ ?_)⟩
    · have := h2.le.trans (min_le_left _ _)
      exact_mod_cast this
    · exact_mod_cast h1
    · have := h2.trans_le (min_le_right _ _); linarith
  · subst heq
    rcases (bot_le : (⊥ : ℝ≥0) ≤ s).lt_or_eq with hpos | h0
    · obtain ⟨ε, hε, H⟩ := hLeft hpos c hcs
      obtain ⟨r, h1, h2⟩ := t10aux (max 0 ((s : ℝ) - ε)) (s : ℝ) (le_max_left _ _)
        (max_lt (by exact_mod_cast hpos) (by linarith))
      refine ⟨r, ?_, lt_max_of_lt_right (H _ ?_ ?_)⟩
      · exact_mod_cast h2.le
      · exact_mod_cast h2
      · have := (le_max_right 0 ((s : ℝ) - ε)).trans_lt h1; linarith
    · subst h0
      rw [show (⊥ : ℝ≥0) = 0 from rfl, hf0] at hcs
      exact absurd hcs (not_lt.mpr (not_lt.mp hc0))
