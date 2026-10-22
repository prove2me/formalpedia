-- Prove2me | solution 2 for GDGen3.D_root_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:55:34.736697+00:00
-- url     : https://prove2.me/submissions/34e916da-1241-4aab-9179-c519c8ff91e4

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_D_root_pos

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N j : ℕ) :
    0 ≤ D r (rootXi r N) N j := by
  by_cases h : j = 0 ∨ N < j
  · simp [D, h]
  · exact le_of_lt (D_root_pos r hr hr1 N j (by omega) (by omega))
