-- Prove2me | solution 2 for GDGen3.rootPoly_actual
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:27:48.181125+00:00
-- url     : https://prove2.me/submissions/f76835af-fc98-40b9-bc21-9c7972bfde7e

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (N i : ℕ) (x : ℝ) :
    rootPoly r (M r N) i x = pj r (i + 1) * x * (1 + x + C r N i) - X r N i := by
  unfold rootPoly C X
  ring
