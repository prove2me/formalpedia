-- Prove2me | solution 1 for BroughanRH.moebius
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @liuyao
-- created : 2026-11-22T14:22:34.306389+00:00
-- url     : https://prove2.me/submissions/99f15471-4126-42f2-b94a-59d8dbcada0f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis

theorem solution :
    ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)) := by
  exact moebius_summatory_rpow_bound_of_riemannHypothesis riemann_hypothesis
