-- Prove2me | solution 2 for GDGen3.rootXi_step_scaled
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:52:36.279584+00:00
-- url     : https://prove2.me/submissions/c9925523-5d93-46ad-b9fc-0e1305c207f7

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_pj_pos
import Theorems.Thm_GDGen3_rootXi_step_bound

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    pj r (i + 1) * rootXi r N i < pj r i * (1 + rootXi r N (i - 1)) := by
  have h := rootXi_step_bound r hr hr1 N i hi hiN hbranch
  have hp := pj_pos r hr hr1 (i + 1) (by omega)
  have hm := mul_lt_mul_of_pos_left h hp
  have he : pj r (i + 1) * (pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1))) =
      pj r i * (1 + rootXi r N (i - 1)) := by field_simp
  rwa [he] at hm
