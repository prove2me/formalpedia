-- Prove2me | solution 1 for FD1D.assignmentCount_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:11.599678+00:00
-- url     : https://prove2.me/submissions/868dfd86-f7c4-4941-9755-db0a96c5f97f

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization
import Theorems.Thm_FD1D_inventoryStatePerm_count
import Theorems.Thm_FD1D_inventoryStatePerm_image_count
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


attribute [local simp] FD1D.inventoryStatePerm_count
attribute [local simp] FD1D.inventoryStatePerm_image_count

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
namespace FD1D
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    {m : ℕ} (e : Equiv.Perm ι) (ω : Assignment ι m) (i : ι) :
    assignmentCount (assignmentPerm e ω) (e i) = assignmentCount ω i := by
  simp [assignmentCount]
end FD1D
