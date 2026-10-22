-- Prove2me | solution 2 for GDGen3.rootXi_eta_last
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:48:19.513363+00:00
-- url     : https://prove2.me/submissions/fee13f42-0731-4a6f-a40c-634ba61b577b

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_pj_pos
import Theorems.Thm_GDGen3_X_last
import Theorems.Thm_GDGen3_rootXi_quad7
import Theorems.Thm_GDGen3_rootXi_nonneg

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
    eta r N (rootXi r N) (N - 1) = 0 := by
  have h := rootXi_quad7 r hr hr1 N (N - 1) (by omega)
  rw [Nat.sub_add_cancel hN, X_last r hr N hN] at h
  have hp : pj r N ≠ 0 := ne_of_gt (pj_pos r hr hr1 N (by omega))
  have hx : 1 + rootXi r N (N - 1) ≠ 0 := by
    have hn := rootXi_nonneg r hr hr1 N (N - 1)
    linarith
  simpa only [mul_eq_zero, hp, hx, false_or, or_false] using h
