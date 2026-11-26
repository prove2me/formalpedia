-- Prove2me | solution 1 for FD1D.inventoryStatePerm_image_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:06.768943+00:00
-- url     : https://prove2.me/submissions/529ee480-957f-431a-af74-2ee237805008

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization
import Theorems.Thm_FD1D_inventoryStatePerm_count
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


attribute [local simp] FD1D.inventoryStatePerm_count

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
namespace FD1D
theorem _root_.solution {ι : Type*} [Fintype ι]
    {m : ℕ} (e : Equiv.Perm ι) (x : InventoryState ι m) (i : ι) :
    (inventoryStatePerm e x).1 (e i) = x.1 i := by
  simp
end FD1D
