-- Prove2me | solution 2 for GDGen3.rootXi_quad
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:39:54.034521+00:00
-- url     : https://prove2.me/submissions/7bf1ff5e-3289-4ebc-a738-163c771fc243

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_pj_pos
import Theorems.Thm_GDGen3_X_zero
import Theorems.Thm_GDGen3_X_pos
import Theorems.Thm_GDGen3_rootXi_zero

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) (hiN : i < N) :
    pj r (i + 1) * rootXi r N i * (1 + eta r N (rootXi r N) i) = X r N i := by
  by_cases hi : i = 0
  · subst i; simp [rootXi_zero, X_zero]
  · have hx := X_pos r hr hr1 N i (by omega) hiN
    have hp := pj_pos r hr hr1 (i + 1) (by omega)
    have hd : 0 ≤ (1 + C r N i) ^ 2 + 4 * X r N i / pj r (i + 1) := by positivity
    have hs := Real.sq_sqrt hd
    unfold eta
    simp only [rootXi, if_neg hi, if_pos hiN]
    have hm : pj r (i + 1) * (4 * X r N i / pj r (i + 1)) = 4 * X r N i :=
      mul_div_cancel₀ _ (ne_of_gt hp)
    nlinarith [hs, hm]
