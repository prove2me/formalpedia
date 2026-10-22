-- Prove2me | solution 2 for GDGen3.rootNu_neg
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:38:18.123355+00:00
-- url     : https://prove2.me/submissions/bb224f1a-459a-4a5d-af43-2392e9a7f4c3

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_pj_pos
import Theorems.Thm_GDGen3_pj_slope_strictMono

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) : rootNu r i < 0 := by
  have h := pj_slope_strictMono r hr hr1 (by omega : i - 1 < i)
  dsimp at h
  rw [Nat.sub_add_cancel hi] at h
  have hci : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast Nat.sub_add_cancel hi
  rw [hci] at h
  have hip : 0 < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hp := pj_pos r hr hr1 i (by omega)
  have hp1 := pj_pos r hr hr1 (i + 1) (by omega)
  have hc := (div_lt_div_iff₀ hip (by positivity)).mp h
  unfold rootNu
  apply sub_neg.mpr
  apply (div_lt_div_iff₀ hp1 hp).2
  nlinarith
