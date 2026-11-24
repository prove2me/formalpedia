-- Prove2me | solution 2 for FairSelling.Examples.PS_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:50:08.070983+00:00
-- url     : https://prove2.me/submissions/eef7d1fb-d706-4a0e-93f4-90e85ef71f3b

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_Examples
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.Examples
namespace FairSelling.Examples
theorem _root_.solution : PS 2 vex pex = 2 := by
  simp only [PS, Fin.sum_univ_two, vex, pex, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num
end FairSelling.Examples
