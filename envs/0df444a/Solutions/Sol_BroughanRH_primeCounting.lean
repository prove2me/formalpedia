-- Prove2me | solution 1 for BroughanRH.primeCounting
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @liuyao
-- created : 2026-11-22T14:22:27.845519+00:00
-- url     : https://prove2.me/submissions/ebf120be-45b0-4912-8d2c-909fb0b60ed6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_VonKoch_primeCounting_sub_logIntegral_of_riemannHypothesis

theorem solution :
    ∃ C : ℝ, ∀ x : ℝ, 3 ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| ≤
        C * Real.sqrt x * Real.log x := by
  exact VonKoch.primeCounting_sub_logIntegral_of_riemannHypothesis riemann_hypothesis
