-- Prove2me | solution 2 for GDGen3.Abar_root_pos
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:48:20.319671+00:00
-- url     : https://prove2.me/submissions/672aaeba-5b39-40b5-a2da-f13f1fd7d382

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_rootXi_pos
import Theorems.Thm_GDGen3_rootXi_nonneg

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) :
    0 < Abar (rootXi r N) i := by
  induction i with
  | zero => simp [Abar]
  | succ i ih =>
    rw [Abar]
    have hx := rootXi_pos r hr hr1 N (i + 1) (by omega)
    have hp := rootXi_nonneg r hr hr1 N i
    exact div_pos (mul_pos ih (by linarith)) hx
