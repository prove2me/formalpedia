-- Prove2me | solution 3 for BroughanRH.chebyshev
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:33:53.99123+00:00
-- url     : https://prove2.me/submissions/0db7e4c4-f5cb-45fc-a4b7-7d8562767042
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_LandauCriterion_psi_error_of_riemannHypothesis


theorem solution :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 2 :=
  LandauCriterion.psi_error_of_riemannHypothesis riemann_hypothesis

