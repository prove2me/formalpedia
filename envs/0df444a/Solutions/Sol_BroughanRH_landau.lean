-- Prove2me | solution 1 for BroughanRH.landau
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @liuyao
-- created : 2026-11-22T14:22:37.907982+00:00
-- url     : https://prove2.me/submissions/2942b7cf-9832-4f40-9572-f8ea0829f849
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_LandauFunction_landau_of_riemannHypothesis

theorem solution :
    ∀ᶠ n : ℕ in Filter.atTop, Real.log (LandauFunction.landau n) < Real.sqrt (LandauFunction.logIntegralInv n) := by
  exact LandauFunction.landau_of_riemannHypothesis riemann_hypothesis
