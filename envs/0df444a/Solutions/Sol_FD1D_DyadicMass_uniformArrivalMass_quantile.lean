-- Prove2me | solution 1 for FD1D.DyadicMass.uniformArrivalMass_quantile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:20:45.487673+00:00
-- url     : https://prove2.me/submissions/87007c48-229c-464e-8c3b-18adbb62c4c8

import Definitions.Def_FD1D_Spatial
import Definitions.Def_FD1D_UniformArrival
import Theorems.Thm_FD1D_DyadicMass_uniformArrivalMass_piecewiseCDF
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_SupplyConfiguration_countState_apply
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.SupplyConfiguration.countState_apply
attribute [local simp] FD1D.weightedLevel_zero


attribute [local simp] FD1D.DyadicMass.uniformArrivalMass_piecewiseCDF

set_option autoImplicit true
open FD1D
noncomputable section
open Set MeasureTheory
open FD1D.DyadicMass
namespace FD1D.DyadicMass
theorem _root_.solution
    (L : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (uniformArrivalMass L).quantile u = u := by
  let q := uniformArrivalMass L
  have hq : q.IsProbability := uniformArrivalMass_isProbability L
  have huTotal : u ≤ q.total := by
    simpa [hq.total_eq_one] using hu.2
  have hquantile :
      q.quantile u ∈ Icc (0 : ℝ) 1 :=
    q.quantile_mem_unit hq.nonneg hu.1 huTotal
  apply le_antisymm
  · apply (q.quantile_le_iff hq.nonneg hu.1 huTotal hu.1 hu.2).2
    change u ≤ (uniformArrivalMass L).piecewiseCDF u
    rw [uniformArrivalMass_piecewiseCDF L hu]
  · have hself :=
      (q.quantile_le_iff hq.nonneg hu.1 huTotal
        hquantile.1 hquantile.2).1 le_rfl
    change u ≤ (uniformArrivalMass L).piecewiseCDF (q.quantile u) at hself
    rw [uniformArrivalMass_piecewiseCDF L hquantile] at hself
    exact hself
end FD1D.DyadicMass
