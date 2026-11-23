-- Prove2me | solution 3 for BroughanRH.landau
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:33:55.930541+00:00
-- url     : https://prove2.me/submissions/de4c6f4c-2cae-4cf7-b6d8-6943d812010e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_LandauFunction_landau_of_riemannHypothesis

theorem solution :
    ∀ᶠ n : ℕ in Filter.atTop, Real.log (LandauFunction.landau n) < Real.sqrt (LandauFunction.logIntegralInv n) :=
  LandauFunction.landau_of_riemannHypothesis riemann_hypothesis
