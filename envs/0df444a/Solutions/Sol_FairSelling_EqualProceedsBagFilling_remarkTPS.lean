-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.remarkTPS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:37:51.031453+00:00
-- url     : https://prove2.me/submissions/f53d58bf-172c-487f-b3a8-532d96232c56

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_EqualProceedsBagFilling
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_TPS_of_zero_val
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_remarkPrice_nonneg

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.EqualProceedsBagFilling
variable {G : Type*} {n : ℕ}
variable {vi p : G → ℝ} {tk : ℝ}
namespace FairSelling.EqualProceedsBagFilling
theorem _root_.solution : TPS 10 (fun _ => (0 : ℝ)) remarkPrice = 99 / 100 := by
  rw [TPS_of_zero_val remarkPrice remarkPrice_nonneg]
  norm_num [remarkPrice, Fin.sum_univ_succ]
end FairSelling.EqualProceedsBagFilling
