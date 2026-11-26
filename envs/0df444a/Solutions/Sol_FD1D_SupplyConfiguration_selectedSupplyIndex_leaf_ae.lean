-- Prove2me | solution 1 for FD1D.SupplyConfiguration.selectedSupplyIndex_leaf_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:33.500369+00:00
-- url     : https://prove2.me/submissions/4d01a8ee-4305-4b2e-8b66-182efeeaabd7

import Definitions.Def_FD1D_Transport
import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Spatial
import Theorems.Thm_FD1D_SupplyConfiguration_countState_apply
import Theorems.Thm_FD1D_SupplyConfiguration_selectedSupplyIndex_leaf_of_ne_zero
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
    (hq : q.IsProbability) (hsupport : C.Supports q)
    (fallback : Fin m) :
    ∀ᵐ u ∂DyadicMass.uniformDemand,
      C.leaf (C.selectedSupplyIndex q fallback u) = q.selectedIndex u := by
  have hne : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
    rw [ae_iff]
    simp only [not_ne_iff]
    rw [show {u : ℝ | u = 0} = ({0} : Set ℝ) by ext u; simp]
    exact measure_singleton 0
  rw [DyadicMass.uniformDemand, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hne] with u hu0 hu
  exact C.selectedSupplyIndex_leaf_of_ne_zero q hq hsupport fallback hu hu0
end FD1D.SupplyConfiguration
