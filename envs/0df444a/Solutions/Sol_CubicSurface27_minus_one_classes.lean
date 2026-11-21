-- Prove2me | solution 1 for CubicSurface27.minus_one_classes
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T02:34:50.310211+00:00
-- url     : https://prove2.me/submissions/82caba1c-f4d8-4ed0-a07a-cb94450c1931

import Mathlib
import Definitions.Def_blowup_lattice_27
open Finset

open CubicSurface27
theorem solution :
    (∀ i : Fin 6, inter (classE i) (classE i) = -1) ∧
    (∀ i j : Fin 6, i ≠ j → inter (lineClass i j) (lineClass i j) = -1) ∧
    (∀ i : Fin 6, inter (conicClass i) (conicClass i) = -1) := by
  decide
