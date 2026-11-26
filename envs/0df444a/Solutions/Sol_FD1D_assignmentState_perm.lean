-- Prove2me | solution 1 for FD1D.assignmentState_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:41:32.499374+00:00
-- url     : https://prove2.me/submissions/1664a8fd-d1cc-4fc3-b395-af3394fd0ae6

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization
import Theorems.Thm_FD1D_inventoryStatePerm_count
import Theorems.Thm_FD1D_inventoryStatePerm_image_count
import Theorems.Thm_FD1D_assignmentCount_perm
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


attribute [local simp] FD1D.inventoryStatePerm_count
attribute [local simp] FD1D.inventoryStatePerm_image_count
attribute [local simp] FD1D.assignmentCount_perm

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
namespace FD1D
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (e : Equiv.Perm ι) (ω : Assignment ι m) :
    assignmentState (assignmentPerm e ω) =
      inventoryStatePerm e (assignmentState ω) := by
  apply InventoryState.ext
  intro i
  change assignmentCount (assignmentPerm e ω) i =
    assignmentCount ω (e.symm i)
  rw [← assignmentCount_perm e ω (e.symm i)]
  simp
end FD1D
