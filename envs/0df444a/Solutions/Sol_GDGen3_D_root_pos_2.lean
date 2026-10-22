-- Prove2me | solution 2 for GDGen3.D_root_pos
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:50:01.024973+00:00
-- url     : https://prove2.me/submissions/0e74e7fa-65dc-4a47-8c58-c62918e8705f

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_pj_pos
import Theorems.Thm_GDGen3_Abar_root_pos

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N j : ℕ)
    (hj : 1 ≤ j) (hjN : j ≤ N) : 0 < D r (rootXi r N) N j := by
  simp only [D, if_neg (by omega : ¬(j = 0 ∨ N < j)), Am, if_neg (by omega : j ≠ 0)]
  exact div_pos (pj_pos r hr hr1 j (by omega)) (Abar_root_pos r hr hr1 N (j - 1))
