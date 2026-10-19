-- Prove2me | solution 1 for Ehrhart.BergmanJetBodyLogPartitionSharpGrowth.momentBodyLogPartition_le_dimension_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/126d3925-e11a-40fe-952b-b7a61c6e0d29

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicUnconditionalBodyConvexity_convexOn_momentBodyLogPartition_Ici
import Theorems.Thm_Ehrhart_BergmanJetLocalEnvelopeGrowth_exists_momentBodyLogPartition_linear_growth

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetBodyLogPartitionSharpGrowth
open Set Filter
open TorusCharacters BergmanJetPartitionEndpoint
open BergmanJetJointHolomorphicUnconditionalBodyConvexity BergmanJetLocalEnvelopeGrowth
open scoped Topology
namespace Ehrhart.BergmanJetBodyLogPartitionSharpGrowth
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    {t : ℝ} (ht : 0 ≤ t) :
    momentBodyLogPartition K (0 : LogSpace n) t ≤
      (n : ℝ) * t := by
  let L := momentBodyLogPartition K (0 : LogSpace n)
  have hconvex : ConvexOn ℝ (Set.Ici 0) L :=
    convexOn_momentBodyLogPartition_Ici K (0 : LogSpace n)
  have hzero : L 0 = 0 :=
    momentBodyLogPartition_zero K (0 : LogSpace n)
  obtain ⟨C, hgrowth⟩ := exists_momentBodyLogPartition_linear_growth K
  change L t ≤ (n : ℝ) * t
  rcases ht.eq_or_lt with rfl | ht'
  · simp [hzero]
  apply (div_le_iff₀ ht').mp
  have hdiv : Tendsto (fun T : ℝ => C / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlim : Tendsto (fun T : ℝ => (n : ℝ) + C / T) atTop (𝓝 n) := by
    simpa only [add_zero] using tendsto_const_nhds.add hdiv
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop t] with T hT
  have hT' := ht'.trans hT
  calc
    L t / t ≤ L T / T := by
      simpa [slope_def_field, hzero] using
        hconvex.monotoneOn_slope_gt
          (show (0 : ℝ) ∈ Set.Ici 0 by simp)
          (show t ∈ {u ∈ Set.Ici (0 : ℝ) | 0 < u} from ⟨ht'.le, ht'⟩)
          (show T ∈ {u ∈ Set.Ici (0 : ℝ) | 0 < u} from ⟨hT'.le, hT'⟩)
          hT.le
    _ ≤ ((n : ℝ) * T + C) / T :=
      (div_le_div_iff_of_pos_right hT').mpr (hgrowth T hT'.le)
    _ = (n : ℝ) + C / T := by field_simp
end Ehrhart.BergmanJetBodyLogPartitionSharpGrowth
