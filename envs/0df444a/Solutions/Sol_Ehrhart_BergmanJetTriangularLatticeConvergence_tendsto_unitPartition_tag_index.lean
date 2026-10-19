-- Prove2me | solution 1 for Ehrhart.BergmanJetTriangularLatticeConvergence.tendsto_unitPartition_tag_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/be8226bb-94d7-4972-80cd-aa04e3bce22b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetTriangularLatticeConvergence
open Set Filter MeasureTheory Metric
open LatticeAsymptotics
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetTriangularLatticeConvergence
theorem _root_.solution {n : ℕ}
    (x : Space n) :
    Tendsto (fun k : ℕ =>
      BoxIntegral.unitPartition.tag (k + 1)
        (BoxIntegral.unitPartition.index (k + 1) x))
      atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun k => norm_nonneg _) ?_
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  let ν : Fin n → ℤ := BoxIntegral.unitPartition.index (k + 1) x
  have hxm : x ∈ BoxIntegral.unitPartition.box (k + 1) ν := by
    apply BoxIntegral.unitPartition.mem_box_iff_index.mpr
    rfl
  have htm : BoxIntegral.unitPartition.tag (k + 1) ν ∈
      BoxIntegral.unitPartition.box (k + 1) ν :=
    BoxIntegral.unitPartition.tag_mem (k + 1) ν
  have hd :
      dist (BoxIntegral.unitPartition.tag (k + 1) ν) x ≤
        1 / ((k + 1 : ℕ) : ℝ) :=
    (Metric.dist_le_diam_of_mem
      (BoxIntegral.Box.isBounded_Icc
        (BoxIntegral.unitPartition.box (k + 1) ν))
      (BoxIntegral.Box.coe_subset_Icc htm)
      (BoxIntegral.Box.coe_subset_Icc hxm)).trans
        (BoxIntegral.unitPartition.diam_boxIcc (k + 1) ν)
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hcast : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_add_right k 1)
  calc
    ‖BoxIntegral.unitPartition.tag (k + 1)
        (BoxIntegral.unitPartition.index (k + 1) x) - x‖ =
        dist (BoxIntegral.unitPartition.tag (k + 1) ν) x := by
          rw [dist_eq_norm]
    _ ≤ 1 / ((k + 1 : ℕ) : ℝ) := hd
    _ ≤ 1 / (k : ℝ) := one_div_le_one_div_of_le hkr hcast
end Ehrhart.BergmanJetTriangularLatticeConvergence
