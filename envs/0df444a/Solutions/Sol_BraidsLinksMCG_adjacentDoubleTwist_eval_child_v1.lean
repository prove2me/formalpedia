-- Prove2me | solution 1 for BraidsLinksMCG.adjacentDoubleTwist_eval_child_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T22:25:42.258471+00:00
-- url     : https://prove2.me/submissions/04c9656e-1fe3-42ae-a55b-1e6a3bddfd86

import Mathlib
import Theorems.Thm_BraidsLinksMCG_adjacentHalfTwistConfig_period_shift_child_v1
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

open BraidsLinksMCG TarchaBraids

theorem solution (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    configProj (n + 2)
      (halfTwistConfig (n + 2) (Fin.last n) (2 * (t : ℝ))) =
      (halfTwistLoop (n + 2) (Fin.last n)).trans
      (halfTwistLoop (n + 2) (Fin.last n)) t := by
  change configProj (n + 2)
      (halfTwistConfig (n + 2) (Fin.last n) (2 * (t : ℝ))) =
    ((halfTwistLoop (n + 2) (Fin.last n)).trans
      (halfTwistLoop (n + 2) (Fin.last n))) t
  rw [Path.trans_apply]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [dif_pos ht]
    rfl
  · rw [dif_neg ht]
    change configProj (n + 2)
      (halfTwistConfig (n + 2) (Fin.last n) (2 * (t : ℝ))) =
        configProj (n + 2)
          (halfTwistConfig (n + 2) (Fin.last n) (2 * (t : ℝ) - 1))
    apply Quotient.sound
    refine ⟨Equiv.swap (strandIdx (Fin.last n))
      (strandIdxSucc (Fin.last n)), ?_⟩
    have htime : (2 * (t : ℝ) - 1) + 1 = 2 * (t : ℝ) := by ring
    have h := adjacentHalfTwistConfig_period_shift_child_v1 n
      (2 * (t : ℝ) - 1)
    rw [htime] at h
    exact h
