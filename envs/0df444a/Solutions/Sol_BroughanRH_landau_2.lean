-- Prove2me | solution 2 for BroughanRH.landau
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:26:15.526217+00:00
-- url     : https://prove2.me/submissions/59d27eaf-4ac5-4252-a804-bfafbeff74bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_LandauFunction_landau_of_riemannHypothesis

theorem solution :
    ∀ᶠ n : ℕ in Filter.atTop, Real.log (LandauFunction.landau n) < Real.sqrt (LandauFunction.logIntegralInv n) :=
  LandauFunction.landau_of_riemannHypothesis mathlib_riemannHypothesis
