-- Prove2me | solution 3 for BroughanRH.moebius
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:33:55.364721+00:00
-- url     : https://prove2.me/submissions/544a858b-148b-42ad-95cf-536bc96efd57
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis

theorem solution :
    ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)) :=
  moebius_summatory_rpow_bound_of_riemannHypothesis riemann_hypothesis
