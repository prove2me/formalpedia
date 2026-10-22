-- Prove2me | solution 2 for GDGen3.rootPoly_parameter
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:36:38.260485+00:00
-- url     : https://prove2.me/submissions/41af59dc-1076-4b80-ba73-72135e9b0c20

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_pj_pos

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (v x : ℝ) (i : ℕ) :
    rootPoly r v i x = rootPoly r (1 + r) i x
      + ((1 + r) - v) * (i + 1) / (1 + r) * ((i : ℝ) / 2 - x) := by
  have hp : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  unfold rootPoly
  field_simp [hp]
  ring
