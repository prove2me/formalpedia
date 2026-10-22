-- Prove2me | solution 1 for GDGen3.X_last
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:21:30.21817+00:00
-- url     : https://prove2.me/submissions/bc5eca85-9797-407b-9003-9807f7e0084e

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (N : ℕ) (hN : 1 ≤ N) : X r N N = 0 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold X M
  field_simp
  ring
