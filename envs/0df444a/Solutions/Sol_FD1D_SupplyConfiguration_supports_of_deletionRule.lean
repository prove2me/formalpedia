-- Prove2me | solution 1 for FD1D.SupplyConfiguration.supports_of_deletionRule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:40:08.955124+00:00
-- url     : https://prove2.me/submissions/e304f9ec-594a-45f7-99d1-8224de4d54c0

import Definitions.Def_FD1D_Transport
import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Spatial
import Theorems.Thm_FD1D_SupplyConfiguration_countState_apply
import Theorems.Thm_FD1D_SupplyConfiguration_supports_of_emptyMass
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


attribute [local simp] FD1D.SupplyConfiguration.countState_apply

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory
open FD1D.SupplyConfiguration
variable {L m : ℕ}
namespace FD1D.SupplyConfiguration
theorem _root_.solution
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (R : DeletionRule (DyadicNode L) m)
    (hmass : ∀ i, q.leafMass i = R.prob C.countState i) :
    C.Supports q := by
  apply C.supports_of_emptyMass q
  intro i hi
  rw [hmass i]
  exact R.empty C.countState i (by simpa using hi)
end FD1D.SupplyConfiguration
