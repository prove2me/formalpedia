-- Prove2me | solution 3 for BroughanRH.primeCounting
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:33:54.847539+00:00
-- url     : https://prove2.me/submissions/b67e904e-b964-4309-aea6-865e933a84fe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_VonKoch_primeCounting_sub_logIntegral_of_riemannHypothesis

theorem solution :
    ∃ C : ℝ, ∀ x : ℝ, 3 ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| ≤
        C * Real.sqrt x * Real.log x :=
  VonKoch.primeCounting_sub_logIntegral_of_riemannHypothesis riemann_hypothesis
