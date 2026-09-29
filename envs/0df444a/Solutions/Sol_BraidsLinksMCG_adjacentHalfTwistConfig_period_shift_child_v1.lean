-- Prove2me | solution 1 for BraidsLinksMCG.adjacentHalfTwistConfig_period_shift_child_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T22:02:33.738335+00:00
-- url     : https://prove2.me/submissions/b21c0548-e7fe-4246-8429-1a2b63c411e6

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Definitions.Def_TarchaBraids_HalfTwist

open BraidsLinksMCG TarchaBraids

theorem solution (n : ℕ) (u : ℝ) :
    (halfTwistConfig (n + 2) (Fin.last n) u).1 =
      (halfTwistConfig (n + 2) (Fin.last n) (u + 1)).1 ∘
        Equiv.swap (strandIdx (n := n + 2) (Fin.last n))
          (strandIdxSucc (n := n + 2) (Fin.last n)) := by
  have hangle : Real.pi * (u + 1) = Real.pi * u + Real.pi := by ring
  have hleft :
      twistPoint ((n : ℝ) + 3 / 2) (-1) u =
        twistPoint ((n : ℝ) + 3 / 2) 1 (u + 1) := by
    apply Complex.ext <;>
      simp [twistPoint, hangle, Real.cos_add_pi, Real.sin_add_pi] <;> ring
  have hright :
      twistPoint ((n : ℝ) + 3 / 2) 1 u =
        twistPoint ((n : ℝ) + 3 / 2) (-1) (u + 1) := by
    apply Complex.ext <;>
      simp [twistPoint, hangle, Real.cos_add_pi, Real.sin_add_pi] <;> ring
  have hab : strandIdx (n := n + 2) (Fin.last n) ≠
      strandIdxSucc (n := n + 2) (Fin.last n) := by
    intro h
    have hv := congrArg (fun k : Fin (n + 2) => (k : ℕ)) h
    simp [strandIdx, strandIdxSucc] at hv
  funext k
  change halfTwistFun (n + 2) (Fin.last n) u k =
    halfTwistFun (n + 2) (Fin.last n) (u + 1)
      (Equiv.swap (strandIdx (n := n + 2) (Fin.last n))
        (strandIdxSucc (n := n + 2) (Fin.last n)) k)
  by_cases hk : k = strandIdx (Fin.last n)
  · subst k
    simp only [Equiv.swap_apply_left]
    rw [halfTwistFun_of_eq u (by simp [strandIdx]),
      halfTwistFun_of_eq_succ (u + 1) (by simp [strandIdxSucc])
        (by simp [strandIdxSucc])]
    exact hleft
  · by_cases hk' : k = strandIdxSucc (Fin.last n)
    · subst k
      simp only [Equiv.swap_apply_right]
      rw [halfTwistFun_of_eq_succ u (by simp [strandIdxSucc])
        (by simp [strandIdxSucc]),
        halfTwistFun_of_eq (u + 1) (by simp [strandIdx])]
      exact hright
    · rw [Equiv.swap_apply_of_ne_of_ne hk hk']
      have hk0 : (k : ℕ) ≠ n := by
        intro h
        apply hk
        exact Fin.ext (by simpa [strandIdx] using h)
      have hk1 : (k : ℕ) ≠ n + 1 := by
        intro h
        apply hk'
        exact Fin.ext (by simpa [strandIdxSucc] using h)
      rw [halfTwistFun_of_fixed u (by simpa [Fin.val_last] using hk0)
          (by simpa [Fin.val_last] using hk1),
        halfTwistFun_of_fixed (u + 1) (by simpa [Fin.val_last] using hk0)
          (by simpa [Fin.val_last] using hk1)]
