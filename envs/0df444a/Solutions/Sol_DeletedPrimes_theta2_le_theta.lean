-- Prove2me | solution 1 for DeletedPrimes.theta2_le_theta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:08:17.898051+00:00
-- url     : https://prove2.me/submissions/28f38cba-37bf-4987-b35f-a0b5dc2b9a2f

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_theta_nonneg
import Theorems.Thm_DeletedPrimes_isRegular_of_theta_lt
import Theorems.Thm_DeletedPrimes_IsRegular_isMSRegular
import Theorems.Thm_DeletedPrimes_theta2_le_of_isMSRegular

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) : theta2 S ≤ theta S := by
  refine le_of_forall_gt_imp_ge_of_dense fun θ hθ => ?_
  have h0 : 0 ≤ θ := le_trans (theta_nonneg S) hθ.le
  exact theta2_le_of_isMSRegular h0 ((isRegular_of_theta_lt hθ).isMSRegular h0)
end DeletedPrimes
