-- Prove2me | solution 1 for GDGen3.rootPoly_expanded
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:23:43.971722+00:00
-- url     : https://prove2.me/submissions/406d589d-3ee1-4ea3-ba9e-ba9f63d1edf9

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_pj_pos

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (v x : ℝ) (i : ℕ) :
    rootPoly r v i x = pj r (i + 1) * x * (1 + x - (1 - r) / (1 + r))
      + v * (i + 1) * x / (1 + r) - v * (i : ℝ) * (i + 1) / (2 * (1 + r))
      + (1 - r) * PiS r i / (1 + r) := by
  have hp : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  unfold rootPoly
  field_simp [hp]
  ring
