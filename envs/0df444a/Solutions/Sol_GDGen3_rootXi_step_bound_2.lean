-- Prove2me | solution 2 for GDGen3.rootXi_step_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:51:00.607999+00:00
-- url     : https://prove2.me/submissions/09c98c04-39bb-4114-97ab-6ef6fd4e2263

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_pj_pos
import Theorems.Thm_GDGen3_X_pos
import Theorems.Thm_GDGen3_rootXi_pos
import Theorems.Thm_GDGen3_rootXi_quad
import Theorems.Thm_GDGen3_rootXi_nonneg
import Theorems.Thm_GDGen3_rootPoly_actual
import Theorems.Thm_GDGen3_quadratic_root_lt
import Theorems.Thm_GDGen3_rootJ_actual_pos
import Theorems.Thm_GDGen3_rootPoly_factor

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    rootXi r N i < pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1)) := by
  have hp := pj_pos r hr hr1 (i + 1) (by omega)
  have hpi := pj_pos r hr hr1 i (by omega)
  have hxp := rootXi_pos r hr hr1 N i (by omega)
  have hx := X_pos r hr hr1 N i hi hiN
  have hprev := rootXi_nonneg r hr hr1 N (i - 1)
  have hj := rootJ_actual_pos r hr hr1 N i hi hiN hbranch
  have hy : 0 < pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1)) := by positivity
  have hpoly : 0 < rootPoly r (M r N) i (pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1))) := by
    rw [rootPoly_factor r hr hr1 N i hi hiN]
    positivity
  rw [rootPoly_actual] at hpoly
  have hroot := rootXi_quad r hr hr1 N i hiN
  unfold eta at hroot
  apply quadratic_root_lt (pj r (i + 1)) (pj r (i + 1) * (1 + C r N i)) (X r N i)
    (rootXi r N i) (pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1))) hp hx hxp (le_of_lt hy)
  · nlinarith [hroot]
  · nlinarith [hpoly]
