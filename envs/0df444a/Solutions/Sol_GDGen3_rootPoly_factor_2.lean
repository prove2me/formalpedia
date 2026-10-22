-- Prove2me | solution 2 for GDGen3.rootPoly_factor
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:45:02.092074+00:00
-- url     : https://prove2.me/submissions/e75f3c06-62b9-4efa-8e14-a5bd7d997bad

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_pj_pos
import Theorems.Thm_GDGen3_rootXi_quad7
import Theorems.Thm_GDGen3_rootPoly_actual

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N) :
    rootPoly r (M r N) i (pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1))) =
      pj r i * (1 + rootXi r N (i - 1)) * rootJ r (M r N) (rootXi r N (i - 1)) i := by
  have hq := rootXi_quad7 r hr hr1 N (i - 1) (by omega)
  rw [Nat.sub_add_cancel hi] at hq
  have hp : pj r i ≠ 0 := ne_of_gt (pj_pos r hr hr1 i (by omega))
  have hp1 : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  have hci : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast Nat.sub_add_cancel hi
  rw [rootPoly_actual, ← hq]
  unfold eta C rootJ rootNu
  rw [Nat.sub_add_cancel hi, hci]
  field_simp [hp, hp1]
  ring
