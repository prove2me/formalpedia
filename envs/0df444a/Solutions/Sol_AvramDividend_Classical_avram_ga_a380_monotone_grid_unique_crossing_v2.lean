-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a380_monotone_grid_unique_crossing_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:55:38.90319+00:00
-- url     : https://prove2.me/submissions/4ea1c540-c5d2-4538-af14-217d4d08d472

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

theorem solution
    {α : Type*} [LinearOrder α] (s : ℕ → α) (hs : StrictMono s)
    (ρ : α) (i k : ℕ)
    (hi : s i < ρ ∧ ρ < s (i + 1))
    (hk : s k < ρ ∧ ρ < s (k + 1)) : i = k := by
  rcases lt_trichotomy i k with hik | hEq | hki
  · have hle : s (i + 1) ≤ s k := hs.monotone (Nat.succ_le_iff.mpr hik)
    exact False.elim ((not_lt_of_ge hle) (hk.1.trans hi.2))
  · exact hEq
  · have hle : s (k + 1) ≤ s i := hs.monotone (Nat.succ_le_iff.mpr hki)
    exact False.elim ((not_lt_of_ge hle) (hi.1.trans hk.2))
