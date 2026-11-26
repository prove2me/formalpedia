-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.massLeft_eq_count_mul_rateLeft
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:20:14.875008+00:00
-- url     : https://prove2.me/submissions/19de4bb0-0dbe-4380-b4eb-6fa674b5d461

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution
    (a p h : ℝ) (x y : ℕ) :
    massLeft a p h x y = (x : ℝ) * rateLeft a p h x y := by
  by_cases hzero : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    simp [massLeft, rateLeft, bias, orderedBias, parentMass, inventory]
  · by_cases hx : x = 0
    · subst x
      have hy : y ≠ 0 := by omega
      have hxy : ¬y ≤ 0 := by omega
      simp [massLeft, rateLeft, bias, orderedBias, hzero, hy, hxy,
        parentMass, inventory]
    · rw [rateLeft, if_neg hzero, if_neg hx]
      field_simp
end FD1D.V5.LocalPolicy
