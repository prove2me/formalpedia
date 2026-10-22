-- Prove2me | solution 2 for GDGen3.rootXi_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:41:31.120979+00:00
-- url     : https://prove2.me/submissions/b4dda921-f399-4c5e-82a5-88883cbfe0c7

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_rootXi_zero
import Theorems.Thm_GDGen3_rootXi_pos

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) : 0 ≤ rootXi r N i := by
  by_cases hi : i = 0
  · subst i; rw [rootXi_zero]
  · exact le_of_lt (rootXi_pos r hr hr1 N i hi)
