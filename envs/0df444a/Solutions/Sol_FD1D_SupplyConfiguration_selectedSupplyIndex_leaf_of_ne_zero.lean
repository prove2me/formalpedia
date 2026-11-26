-- Prove2me | solution 1 for FD1D.SupplyConfiguration.selectedSupplyIndex_leaf_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:39:26.120828+00:00
-- url     : https://prove2.me/submissions/9e3c3e23-0031-4a05-aa69-65e8061ac9f5

import Definitions.Def_FD1D_Transport
import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Spatial
import Theorems.Thm_FD1D_SupplyConfiguration_countState_apply
import Theorems.Thm_FD1D_SupplyConfiguration_representative_leaf
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
    (fallback : Fin m) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hu0 : u ≠ 0) :
    C.leaf (C.selectedSupplyIndex q fallback u) = q.selectedIndex u := by
  have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
  have huTotal : u ≤ q.total := by
    simpa [hq.total_eq_one] using hu.2
  have hinter := (q.selectedIndex_eq_iff_mem_massInterval hq.nonneg
    huPos huTotal (q.selectedIndex u)).mp rfl
  have hmass : 0 < q.leafMass (q.selectedIndex u) := by
    linarith [hinter.1, hinter.2]
  exact C.representative_leaf fallback (q.selectedIndex u)
    (hsupport _ hmass)
end FD1D.SupplyConfiguration
