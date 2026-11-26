-- Prove2me | solution 1 for FD1D.SupplyConfiguration.quantile_mem_selectedCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:36:27.3818+00:00
-- url     : https://prove2.me/submissions/b71a29f5-41cc-48b6-b7ad-3f7feb4ee0fa

import Definitions.Def_FD1D_Transport
import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Spatial
import Theorems.Thm_FD1D_DyadicMass_selectedLeaf_eq_selectedIndex
import Theorems.Thm_FD1D_DyadicMass_selectedLeaf_le_quantile
import Theorems.Thm_FD1D_SupplyConfiguration_countState_apply
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
    (q : DyadicMass L) (hq : q.IsProbability)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    q.quantile u ∈ dyadicCell (q.selectedIndex u) := by
  have huTotal : u ≤ q.total := by
    simpa [hq.total_eq_one] using hu.2
  have hle := q.selectedLeaf_le_quantile hq.nonneg hu.1 huTotal
  have hclose := q.selectedLeaf_sub_quantile_le hq.nonneg hu.1 huTotal
  have hleft :
      dyadicCellLeft (q.selectedIndex u) = q.selectedLeaf u := by
    simpa [dyadicCellLeft] using (q.selectedLeaf_eq_selectedIndex u).symm
  rw [dyadicCell, hleft]
  constructor
  · exact hle
  · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hclose
    simpa [dyadicCellWidth] using
      (show q.quantile u ≤ q.selectedLeaf u +
          1 / ((2 ^ L : ℕ) : ℝ) by linarith)
end FD1D.SupplyConfiguration
