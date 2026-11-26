-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.rateLeft_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:21:46.530797+00:00
-- url     : https://prove2.me/submissions/14d698fd-6bb3-46a6-8410-f8355d004ef4

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_LocalPolicy
import Theorems.Thm_FD1D_V5_LocalPolicy_massLeft_swap
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution (a p h : ℝ) (x y : ℕ) :
    rateLeft a p h y x = rateRight a p h x y := by
  unfold rateLeft rateRight
  rw [Nat.add_comm]
  by_cases hzero : x + y = 0
  · simp [hzero]
  · simp only [if_neg hzero]
    by_cases hx : x = 0
    · subst x
      simp at hzero
      simp [hzero, massLeft_swap]
    · by_cases hy : y = 0
      · subst y
        simp [hx]
      · simp [hx, hy, massLeft_swap]
end FD1D.V5.LocalPolicy
