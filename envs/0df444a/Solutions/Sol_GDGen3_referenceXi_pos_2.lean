-- Prove2me | solution 2 for GDGen3.referenceXi_pos
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:36:55.046844+00:00
-- url     : https://prove2.me/submissions/279fbff8-df0b-432e-9e13-4179e05e83a3

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_reference_power_bound

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) : 0 < referenceXi r i := by
  have h := reference_power_bound r hr hr1 N i hi hiN hbranch
  unfold referenceXi
  exact div_pos (by linarith) (by positivity)
