-- Prove2me | solution 1 for FD1D.DyadicMass.uniformArrival_mem_dyadicCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:45:44.532447+00:00
-- url     : https://prove2.me/submissions/746444ad-0342-40fd-85d0-aae134a47417

import Definitions.Def_FD1D_Spatial
import Definitions.Def_FD1D_UniformArrival
import Theorems.Thm_FD1D_DyadicMass_uniformArrivalMass_piecewiseCDF
import Theorems.Thm_FD1D_DyadicMass_uniformArrivalMass_quantile
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_SupplyConfiguration_countState_apply
import Theorems.Thm_FD1D_SupplyConfiguration_quantile_mem_selectedCell
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.SupplyConfiguration.countState_apply
attribute [local simp] FD1D.weightedLevel_zero


attribute [local simp] FD1D.DyadicMass.uniformArrivalMass_piecewiseCDF
attribute [local simp] FD1D.DyadicMass.uniformArrivalMass_quantile

set_option autoImplicit true
open FD1D
noncomputable section
open Set MeasureTheory
open FD1D.DyadicMass
namespace FD1D.DyadicMass
theorem _root_.solution
    (L : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    u ∈ dyadicCell (uniformArrivalLeaf L u) := by
  have hcell :=
    SupplyConfiguration.quantile_mem_selectedCell
      (uniformArrivalMass L) (uniformArrivalMass_isProbability L) hu
  rw [uniformArrivalMass_quantile L hu] at hcell
  simpa [uniformArrivalLeaf] using hcell
end FD1D.DyadicMass
