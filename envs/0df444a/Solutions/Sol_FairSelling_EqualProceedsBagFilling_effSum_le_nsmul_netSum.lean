-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.effSum_le_nsmul_netSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:36:02.768996+00:00
-- url     : https://prove2.me/submissions/88d7e599-0b1c-48e7-bc9f-b04945a80b63

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_EqualProceedsBagFilling
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_effVal_le_nsmul_netVal

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.EqualProceedsBagFilling
variable {G : Type*} {n : ℕ}
variable {vi p : G → ℝ} {tk : ℝ}
namespace FairSelling.EqualProceedsBagFilling
theorem _root_.solution (hv : ∀ g, 0 ≤ vi g) (ht : 0 ≤ tk)
    (hn : 0 < n) (B : Finset G) :
    effSum vi p tk B ≤ (n : ℝ) * netSum n vi p tk B := by
  unfold effSum netSum
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun g _ => effVal_le_nsmul_netVal hv ht hn g
end FairSelling.EqualProceedsBagFilling
