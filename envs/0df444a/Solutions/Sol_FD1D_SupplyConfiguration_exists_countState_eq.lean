-- Prove2me | solution 1 for FD1D.SupplyConfiguration.exists_countState_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:05:45.084931+00:00
-- url     : https://prove2.me/submissions/05f7c1b0-24e1-4cd0-9fdf-33effada5294

import Definitions.Def_FD1D_Spatial
import Definitions.Def_FD1D_Realization
import Theorems.Thm_FD1D_SupplyConfiguration_ofCountState_countState
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_SupplyConfiguration_countState_apply
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.SupplyConfiguration.countState_apply
attribute [local simp] FD1D.weightedLevel_zero


attribute [local simp] FD1D.SupplyConfiguration.ofCountState_countState

set_option autoImplicit true
open FD1D
noncomputable section
open Set
open FD1D.SupplyConfiguration
variable {L m : ℕ}
namespace FD1D.SupplyConfiguration
theorem _root_.solution
    (x : InventoryState (DyadicNode L) m) :
    ∃ C : SupplyConfiguration L m, C.countState = x :=
  ⟨ofCountState x, ofCountState_countState x⟩
end FD1D.SupplyConfiguration
