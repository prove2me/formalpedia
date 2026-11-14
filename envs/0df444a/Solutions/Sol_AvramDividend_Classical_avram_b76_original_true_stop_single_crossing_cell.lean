-- Prove2me | solution 1 for AvramDividend.Classical.avram_b76_original_true_stop_single_crossing_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:57:43.400196+00:00
-- url     : https://prove2.me/submissions/e397fbc4-fb31-44ce-8543-af6d0ed575a8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter
open scoped NNReal
noncomputable section

/-- A true clipped increasing grid has at most one cell entering its terminal stopping clock. -/
theorem solution
    {Ω : Type*} (u : ℕ → ℝ≥0) (hu : StrictMono u)
    (κ : Ω → ℝ≥0) (ω : Ω) (i j : ℕ)
    (hiBefore : min (u i) (κ ω) < κ ω)
    (hiContact : min (u (i + 1)) (κ ω) = κ ω)
    (hjBefore : min (u j) (κ ω) < κ ω)
    (hjContact : min (u (j + 1)) (κ ω) = κ ω) :
    i = j := by
  have hiLow : u i < κ ω := by
    by_contra hn
    have hle : κ ω ≤ u i := le_of_not_gt hn
    have heq : min (u i) (κ ω) = κ ω := min_eq_right hle
    rw [heq] at hiBefore
    exact (lt_irrefl (κ ω)) hiBefore
  have hjLow : u j < κ ω := by
    by_contra hn
    have hle : κ ω ≤ u j := le_of_not_gt hn
    have heq : min (u j) (κ ω) = κ ω := min_eq_right hle
    rw [heq] at hjBefore
    exact (lt_irrefl (κ ω)) hjBefore
  have hiHigh : κ ω ≤ u (i + 1) := by
    calc
      κ ω = min (u (i + 1)) (κ ω) := hiContact.symm
      _ ≤ u (i + 1) := min_le_left _ _
  have hjHigh : κ ω ≤ u (j + 1) := by
    calc
      κ ω = min (u (j + 1)) (κ ω) := hjContact.symm
      _ ≤ u (j + 1) := min_le_left _ _
  rcases lt_trichotomy i j with hij | heq | hji
  · have hStep : i + 1 ≤ j := Nat.succ_le_iff.mpr hij
    have hbad : κ ω ≤ u j := hiHigh.trans (hu.monotone hStep)
    exact False.elim ((not_lt_of_ge hbad) hjLow)
  · exact heq
  · have hStep : j + 1 ≤ i := Nat.succ_le_iff.mpr hji
    have hbad : κ ω ≤ u i := hjHigh.trans (hu.monotone hStep)
    exact False.elim ((not_lt_of_ge hbad) hiLow)
