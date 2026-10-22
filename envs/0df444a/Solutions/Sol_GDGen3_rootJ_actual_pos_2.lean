-- Prove2me | solution 2 for GDGen3.rootJ_actual_pos
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:49:32.005232+00:00
-- url     : https://prove2.me/submissions/582ef142-72ca-4968-b932-f65d6f5ef3d2

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_pj_pos
import Theorems.Thm_GDGen3_M_le_h
import Theorems.Thm_GDGen3_rootXi_le_reference
import Theorems.Thm_GDGen3_rootNu_neg
import Theorems.Thm_GDGen3_pj_strictMono
import Theorems.Thm_GDGen3_rootJ_reference_pos

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    0 < rootJ r (M r N) (rootXi r N (i - 1)) i := by
  have href := rootJ_reference_pos r hr hr1 i hi
  have hxi := rootXi_le_reference r hr hr1 N (i - 1) (by omega) hbranch
  have hm := M_le_h r hr hr1 N (by omega) hbranch
  have hnu := rootNu_neg r hr hr1 i hi
  have hpp := pj_strictMono r hr hr1 (by omega : i < i + 1)
  have hp1 := pj_pos r hr hr1 (i + 1) (by omega)
  have hk : 0 < 1 - pj r i / pj r (i + 1) := by
    apply sub_pos.mpr
    exact (div_lt_one hp1).2 hpp
  have hmdiv : M r N / (1 + r) ≤ 1 := (div_le_one (by positivity)).2 hm
  have hnu2 := mul_le_mul_of_nonpos_right hmdiv (le_of_lt hnu)
  have hxi2 := mul_le_mul_of_nonneg_left hxi (le_of_lt hk)
  unfold rootJ at *
  have hh : (1 + r) / (1 + r) = (1 : ℝ) := div_self (by positivity)
  rw [hh] at href
  nlinarith
