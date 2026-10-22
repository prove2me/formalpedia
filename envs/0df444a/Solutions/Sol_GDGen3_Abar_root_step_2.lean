-- Prove2me | solution 2 for GDGen3.Abar_root_step
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:55:34.017989+00:00
-- url     : https://prove2.me/submissions/6f0c565a-f889-44a8-8ce3-f0c67dcc2dcd

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_pj_pos
import Theorems.Thm_GDGen3_rootXi_pos
import Theorems.Thm_GDGen3_rootXi_nonneg
import Theorems.Thm_GDGen3_pj_strictMono
import Theorems.Thm_GDGen3_Abar_root_pos
import Theorems.Thm_GDGen3_Abar_root_recur
import Theorems.Thm_GDGen3_rootXi_step_scaled

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    Abar (rootXi r N) (i - 1) < Abar (rootXi r N) i := by
  have hx := rootXi_pos r hr hr1 N i (by omega)
  have hprev := rootXi_nonneg r hr hr1 N (i - 1)
  have hA := Abar_root_pos r hr hr1 N (i - 1)
  have hsc := rootXi_step_scaled r hr hr1 N i hi hiN hbranch
  have hpp := pj_strictMono r hr hr1 (by omega : i < i + 1)
  have hp := pj_pos r hr hr1 i (by omega)
  have hmult := mul_lt_mul_of_pos_right hpp hx
  have hless : rootXi r N i < 1 + rootXi r N (i - 1) := by
    have h0 : pj r i * rootXi r N i < pj r i * (1 + rootXi r N (i - 1)) := by linarith
    exact (mul_lt_mul_iff_right₀ hp).mp h0
  rw [Abar_root_recur r N i hi]
  apply (lt_div_iff₀ hx).2
  exact mul_lt_mul_of_pos_left hless hA
