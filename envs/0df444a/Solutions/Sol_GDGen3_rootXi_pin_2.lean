-- Prove2me | solution 2 for GDGen3.rootXi_pin
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:50:42.884345+00:00
-- url     : https://prove2.me/submissions/40000036-30b6-4b30-9e8a-46b2284a4e65

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_rootXi_quad
import Theorems.Thm_GDGen3_rootXi_eta_last

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
    pj r N * rootXi r N (N - 1) = X r N (N - 1) := by
  have h := rootXi_quad r hr hr1 N (N - 1) (by omega)
  simpa only [Nat.sub_add_cancel hN, rootXi_eta_last r hr hr1 N hN, add_zero, mul_one] using h
