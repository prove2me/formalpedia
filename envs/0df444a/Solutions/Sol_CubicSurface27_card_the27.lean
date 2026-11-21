-- Prove2me | solution 1 for CubicSurface27.card_the27
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T02:34:50.124708+00:00
-- url     : https://prove2.me/submissions/67b819b2-fede-4bb2-8939-b4e22c2c3290

import Mathlib
import Definitions.Def_blowup_lattice_27
open Finset

open CubicSurface27
theorem solution : the27.card = 27 := by
  decide
