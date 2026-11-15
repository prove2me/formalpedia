-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a416_monotone_grid_unique_inclusive_crossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:36:32.380231+00:00
-- url     : https://prove2.me/submissions/0a518080-b3f1-459d-b566-a477c2b9a224

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

theorem solution
    {α : Type*} [LinearOrder α] (s : ℕ → α) (hs : StrictMono s)
    (ρ : α) (i j : ℕ)
    (hi : s i < ρ ∧ ρ ≤ s (i + 1))
    (hj : s j < ρ ∧ ρ ≤ s (j + 1)) : i = j := by
  rcases lt_trichotomy i j with hij | heq | hji
  · have hle : s (i + 1) ≤ s j :=
      hs.monotone (Nat.succ_le_iff.mpr hij)
    exact False.elim ((not_lt_of_ge (hi.2.trans hle)) hj.1)
  · exact heq
  · have hle : s (j + 1) ≤ s i :=
      hs.monotone (Nat.succ_le_iff.mpr hji)
    exact False.elim ((not_lt_of_ge (hj.2.trans hle)) hi.1)
