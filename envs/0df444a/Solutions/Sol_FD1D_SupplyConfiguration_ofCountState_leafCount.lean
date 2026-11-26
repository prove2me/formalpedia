-- Prove2me | solution 1 for FD1D.SupplyConfiguration.ofCountState_leafCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:43:20.371948+00:00
-- url     : https://prove2.me/submissions/f1a0049c-f678-4497-93f0-641e9132c044

import Definitions.Def_FD1D_Spatial
import Definitions.Def_FD1D_Realization
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_SupplyConfiguration_countState_apply
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.SupplyConfiguration.countState_apply
attribute [local simp] FD1D.weightedLevel_zero


section
namespace FD1D
noncomputable section
open Set
namespace SupplyConfiguration
variable {L m : ℕ}
private theorem countAssignment_fiber_card
    (x : InventoryState (DyadicNode L) m) (i : DyadicNode L) :
    (Finset.univ.filter fun j : Fin m => countAssignment x j = i).card =
      x.1 i := by
  rw [← Fintype.card_coe
    (Finset.univ.filter fun j : Fin m => countAssignment x j = i)]
  simpa only [Fintype.card_fin] using
    Fintype.card_congr (countAssignmentFiberEquiv x i)
end SupplyConfiguration
end
end FD1D
end

set_option autoImplicit true
open FD1D
noncomputable section
open Set
open FD1D.SupplyConfiguration
variable {L m : ℕ}
namespace FD1D.SupplyConfiguration
theorem _root_.solution
    (x : InventoryState (DyadicNode L) m) (i : DyadicNode L) :
    (ofCountState x).leafCount i = x.1 i := by
  change
    (Finset.univ.filter fun j : Fin m => countAssignment x j = i).card =
      x.1 i
  exact countAssignment_fiber_card x i
end FD1D.SupplyConfiguration
