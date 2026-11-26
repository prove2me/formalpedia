-- Prove2me | solution 1 for FD1D.SupplyConfiguration.ofCountState_countState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:45:07.257931+00:00
-- url     : https://prove2.me/submissions/63823805-e326-495f-8577-335d6ba1773a

import Definitions.Def_FD1D_Spatial
import Definitions.Def_FD1D_Realization
import Theorems.Thm_FD1D_SupplyConfiguration_ofCountState_location
import Theorems.Thm_FD1D_SupplyConfiguration_ofCountState_leafCount
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_SupplyConfiguration_countState_apply
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.SupplyConfiguration.countState_apply
attribute [local simp] FD1D.weightedLevel_zero


attribute [local simp] FD1D.SupplyConfiguration.ofCountState_location
attribute [local simp] FD1D.SupplyConfiguration.ofCountState_leafCount

set_option autoImplicit true
open FD1D
noncomputable section
open Set
open FD1D.SupplyConfiguration
variable {L m : ℕ}
namespace FD1D.SupplyConfiguration
theorem _root_.solution
    (x : InventoryState (DyadicNode L) m) :
    (ofCountState x).countState = x := by
  apply InventoryState.ext
  intro i
  exact ofCountState_leafCount x i
end FD1D.SupplyConfiguration
