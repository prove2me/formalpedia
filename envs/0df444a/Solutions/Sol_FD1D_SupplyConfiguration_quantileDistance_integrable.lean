-- Prove2me | solution 1 for FD1D.SupplyConfiguration.quantileDistance_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:39:59.491543+00:00
-- url     : https://prove2.me/submissions/2873dea0-3981-4cfa-a275-e5c83b4ab66f

import Definitions.Def_FD1D_Transport
import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Spatial
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
    (q : DyadicMass L) (hq : q.IsProbability) :
    IntegrableOn (fun u => |q.quantile u - u|) (Icc (0 : ℝ) 1) := by
  apply Measure.integrableOn_of_bounded (by simp [Real.volume_Icc])
    (q.quantile_measurable.sub measurable_id).abs.aestronglyMeasurable (M := 1)
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro u hu
  change ‖|q.quantile u - u|‖ ≤ 1
  rw [Real.norm_eq_abs, abs_abs]
  have hqUnit := q.quantile_mem_unit hq.nonneg hu.1
    (by simpa [hq.total_eq_one] using hu.2)
  exact abs_le.2
    ⟨by linarith [hqUnit.1, hu.2], by linarith [hqUnit.2, hu.1]⟩
end FD1D.SupplyConfiguration
