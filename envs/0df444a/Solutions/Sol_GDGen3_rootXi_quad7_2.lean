-- Prove2me | solution 2 for GDGen3.rootXi_quad7
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:43:02.428383+00:00
-- url     : https://prove2.me/submissions/e302a607-7a59-4ee4-8820-ac675dfb71ce

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_X_step
import Theorems.Thm_GDGen3_rootXi_quad

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) (hiN : i < N) :
    pj r (i + 1) * eta r N (rootXi r N) i * (1 + rootXi r N i) = X r N (i + 1) := by
  have hq := rootXi_quad r hr hr1 N i hiN
  have hx := X_step r hr hr1 N i
  unfold eta at *
  linear_combination hq - hx
