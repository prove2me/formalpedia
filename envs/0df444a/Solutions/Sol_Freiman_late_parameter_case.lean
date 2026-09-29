-- Prove2me | solution 1 for Freiman.late_parameter_case
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T18:13:58.142034+00:00
-- url     : https://prove2.me/submissions/44836207-c6f1-4f67-b7c1-1bb3a33cdc55

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.List.Infix

set_option maxHeartbeats 1000000

open Freiman

namespace M7Last

/-- The continuant denominator of any word is at least 1 (and the numerator is a `ℕ`). -/
lemma cd_den_pos_aux (w : List ℕ+) :
    ∀ c d : ℕ, 1 ≤ d →
      1 ≤ (w.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) (c, d)).2 := by
  induction w with
  | nil => intro c d hd; exact hd
  | cons a t ih =>
      intro c d hd
      refine ih d (c + (a : ℕ) * d) ?_
      have ha : 1 ≤ (a : ℕ) := a.one_le
      calc (1:ℕ) = 1 * 1 := by norm_num
        _ ≤ (a : ℕ) * d := Nat.mul_le_mul ha hd
        _ ≤ c + (a : ℕ) * d := Nat.le_add_left _ _

lemma cd_den_pos (w : List ℕ+) : 1 ≤ (lowerCD w).2 :=
  cd_den_pos_aux w 0 1 (le_refl 1)

/-- A word ending in the letter `3` has continuant ratio at most `1/3`. -/
lemma ratio_le_third (v : List ℕ+) (h : lowerEnds v [3]) : lowerRatio v ≤ (1/3 : ℝ) := by
  obtain ⟨u, rfl⟩ := h
  have hcd : lowerCD (u ++ [3]) = ((lowerCD u).2, (lowerCD u).1 + 3 * (lowerCD u).2) := by
    simp [lowerCD, List.foldl_append]
  set C := (lowerCD u).1 with hC
  set D := (lowerCD u).2 with hD
  have hD1 : 1 ≤ D := cd_den_pos u
  have hDR : (1:ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hCR : (0:ℝ) ≤ (C : ℝ) := Nat.cast_nonneg _
  have hden : (0:ℝ) < ((C + 3 * D : ℕ) : ℝ) := by
    push_cast; linarith
  rw [lowerRatio, hcd]
  simp only
  rw [div_le_iff₀ hden]
  push_cast
  linarith

end M7Last

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p)
    (hd : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p)
    (hr : (13/17 : ℝ) ≤ lowerRatio (lowerNormalize p).1) :
    ∃ right3 : Bool, lateMatches p right3 ∧
      certRectangleMem (lateRootRectangle right3) (lateR p) (lateS p) := by
  classical
  obtain ⟨hadm, hgood, hcov, hbox⟩ := hs
  -- the parameter box for the normalized pair
  have hbox' : (1/4 : ℝ) ≤ lowerRatio (lowerNormalize p).1 ∧
      lowerRatio (lowerNormalize p).1 ≤ (4/5 : ℝ) ∧
      (1/4 : ℝ) ≤ lowerRatio (lowerNormalize p).2 ∧
      lowerRatio (lowerNormalize p).2 ≤ (4/5 : ℝ) := by
    unfold lowerNormalize
    by_cases hw : lowerWidth p.2 ≤ lowerWidth p.1
    · simp only [hw, if_true]
      exact ⟨hbox.1, hbox.2.1, hbox.2.2.1, hbox.2.2.2⟩
    · simp only [hw, if_false]
      exact ⟨hbox.2.2.1, hbox.2.2.2, hbox.1, hbox.2.1⟩
  by_cases h3 : lowerEnds (lowerNormalize p).2 [3]
  · refine ⟨true, ⟨hd.1, hd.2.2.2.1, ?_⟩, ?_⟩
    · exact ⟨fun _ => h3, fun _ => rfl⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · show ((13/17 : ℚ) : ℝ) ≤ lateR p
        rw [lateR]; push_cast; linarith [hr]
      · show lateR p ≤ ((4/5 : ℚ) : ℝ)
        rw [lateR]; push_cast; linarith [hbox'.2.1]
      · show ((1/4 : ℚ) : ℝ) ≤ lateS p
        rw [lateS]; push_cast; linarith [hbox'.2.2.1]
      · show lateS p ≤ (((if true then 1/3 else 4/5 : ℚ)) : ℝ)
        rw [lateS]
        simp only [if_true]
        push_cast
        exact M7Last.ratio_le_third _ h3
  · refine ⟨false, ⟨hd.1, hd.2.2.2.1, ?_⟩, ?_⟩
    · constructor
      · intro h; exact absurd h (by decide)
      · intro h; exact absurd h h3
    · refine ⟨?_, ?_, ?_, ?_⟩
      · show ((13/17 : ℚ) : ℝ) ≤ lateR p
        rw [lateR]; push_cast; linarith [hr]
      · show lateR p ≤ ((4/5 : ℚ) : ℝ)
        rw [lateR]; push_cast; linarith [hbox'.2.1]
      · show ((1/4 : ℚ) : ℝ) ≤ lateS p
        rw [lateS]; push_cast; linarith [hbox'.2.2.1]
      · show lateS p ≤ (((if false then 1/3 else 4/5 : ℚ)) : ℝ)
        rw [lateS]
        push_cast
        linarith [hbox'.2.2.2]
