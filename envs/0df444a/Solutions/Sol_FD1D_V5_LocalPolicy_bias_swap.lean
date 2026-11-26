-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.bias_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:33.658875+00:00
-- url     : https://prove2.me/submissions/1ed169c5-ee30-4764-9219-a2e686ac95b1

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_LocalPolicy
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution (a p h : ℝ) (x y : ℕ) :
    bias a p h y x = -bias a p h x y := by
  unfold bias
  by_cases hxy : y ≤ x
  · by_cases hyx : x ≤ y
    · have hEq : x = y := Nat.le_antisymm hyx hxy
      subst y
      simp [orderedBias]
    · simp [hxy, hyx]
  · have hyx : x ≤ y := Nat.le_of_not_ge hxy
    simp [hxy, hyx]
end FD1D.V5.LocalPolicy
