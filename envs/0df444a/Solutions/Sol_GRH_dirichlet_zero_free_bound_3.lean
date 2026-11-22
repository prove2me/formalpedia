-- Prove2me | solution 3 for GRH.dirichlet_zero_free_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-21T16:55:44.478183+00:00
-- url     : https://prove2.me/submissions/25a02c01-5be1-4074-93c8-14ad04cb9fff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlpoGe_galoisLocalGlobalStrong_recParameter
import Theorems.Thm_AlpoGe_everyCharacter_of_row

theorem solution
    {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (1 / 2 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  AlpoGe.everyCharacter_of_row AlpoGe.galoisLocalGlobalStrong_recParameter q χ s hs
    (not_and_or.mp hpole)
