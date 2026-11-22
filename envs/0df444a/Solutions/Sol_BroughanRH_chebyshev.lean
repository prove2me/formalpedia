-- Prove2me | solution 1 for BroughanRH.chebyshev
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @liuyao
-- created : 2026-11-22T14:22:31.528842+00:00
-- url     : https://prove2.me/submissions/5823735c-ff4b-49c1-8d8f-b76ac1212889
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_LandauCriterion_psi_error_of_riemannHypothesis

theorem solution :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 2 := by
  exact LandauCriterion.psi_error_of_riemannHypothesis riemann_hypothesis
