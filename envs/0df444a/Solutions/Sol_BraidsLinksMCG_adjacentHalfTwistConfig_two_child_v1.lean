-- Prove2me | solution 1 for BraidsLinksMCG.adjacentHalfTwistConfig_two_child_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T21:43:37.761569+00:00
-- url     : https://prove2.me/submissions/a9239e16-2540-4875-843c-6d2c5c91738a

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

open BraidsLinksMCG TarchaBraids

theorem solution (n : ℕ) :
    halfTwistConfig (n + 2) (Fin.last n) 2 = baseOrdered (n + 2) := by
  apply Subtype.ext
  funext k
  by_cases hk : (k : ℕ) = n
  · change halfTwistFun (n + 2) (Fin.last n) 2 k = _
    rw [halfTwistFun_of_eq 2 (by simpa [Fin.val_last] using hk)]
    have hangle : Real.pi * 2 = 2 * Real.pi := by ring
    apply Complex.ext <;>
      simp [twistPoint_re, twistPoint_im, baseOrdered, hangle, hk,
        Real.cos_two_pi, Real.sin_two_pi] <;> push_cast <;> ring
  · by_cases hk' : (k : ℕ) = n + 1
    · change halfTwistFun (n + 2) (Fin.last n) 2 k = _
      rw [halfTwistFun_of_eq_succ 2 (by simpa [Fin.val_last] using hk)
        (by simpa [Fin.val_last] using hk')]
      have hangle : Real.pi * 2 = 2 * Real.pi := by ring
      apply Complex.ext <;>
        simp [twistPoint_re, twistPoint_im, baseOrdered, hangle, hk',
          Real.cos_two_pi, Real.sin_two_pi] <;> push_cast <;> ring
    · change halfTwistFun (n + 2) (Fin.last n) 2 k = _
      rw [halfTwistFun_of_fixed 2 (by simpa [Fin.val_last] using hk)
        (by simpa [Fin.val_last] using hk')]
      simp [baseOrdered]
