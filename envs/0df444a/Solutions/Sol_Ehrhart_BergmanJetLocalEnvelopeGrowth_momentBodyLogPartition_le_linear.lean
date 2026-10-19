-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalEnvelopeGrowth.momentBodyLogPartition_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/a5c8854b-eb32-412f-b7f6-5fdb029cd8a6

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourceLocalBallVolumeConstant_pos
import Theorems.Thm_Ehrhart_BergmanJetPartitionEndpoint_momentBodyLogPartition_eq_sourceLogPartition_add_log_volume
import Theorems.Thm_Ehrhart_BergmanJetLocalEnvelopeGrowth_momentBodyPartition_ge_local_box

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetLocalEnvelopeGrowth
open Set Function Filter MeasureTheory Module Metric
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open BergmanJetUpperEnvelope BergmanJetEnvelopeLimit BergmanJetTorusEnvelope
open BergmanJetPartitionEndpoint BergmanJetLocalGrowth ActualJetUpperEnvelope
open JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative JetEnvelopeLocalGrowth
open LogPartitionConvexity
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetLocalEnvelopeGrowth
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (R t : ℝ) (hR : 0 < R) (ht : 0 < t) :
    momentBodyLogPartition K (0 : LogSpace n) t ≤
      (n : ℝ) * t + momentBodyLocalPartitionGrowthConstant K R := by
  have hconstant := sourceLocalBallVolumeConstant_pos n hR
  have hleft : 0 <
      Real.exp
        (-momentLocalPotentialMaximum K
          (momentBodyOptimizer K) (0 : LogSpace n) R) *
        sourceLocalBallVolumeConstant n R *
          Real.exp (-(n : ℝ) * t) := by
    positivity
  have hbound := momentBodyPartition_ge_local_box K R t hR ht
  have hpartition := momentBodyPartition_pos
    K (0 : LogSpace n) t
  have hlog := Real.strictMonoOn_log.monotoneOn
    hleft hpartition hbound
  rw [momentBodyLogPartition_eq_sourceLogPartition_add_log_volume]
  unfold sourceLogPartition momentBodyPartition
    momentBodyLocalPartitionGrowthConstant at *
  calc
    -Real.log
      (sourcePartition (momentBodyTorusWeight
        K (0 : LogSpace n)) t) +
          Real.log (normalizedVolume K.carrier) ≤
      -Real.log
        (Real.exp
          (-momentLocalPotentialMaximum K
            (momentBodyOptimizer K) (0 : LogSpace n) R) *
          sourceLocalBallVolumeConstant n R *
          Real.exp (-(n : ℝ) * t)) +
            Real.log (normalizedVolume K.carrier) := by
        linarith
    _ = (n : ℝ) * t +
        (momentLocalPotentialMaximum K
          (momentBodyOptimizer K) (0 : LogSpace n) R -
            Real.log (sourceLocalBallVolumeConstant n R) +
              Real.log (normalizedVolume K.carrier)) := by
      rw [Real.log_mul
        (mul_ne_zero (Real.exp_ne_zero _) hconstant.ne')
          (Real.exp_ne_zero _),
        Real.log_mul (Real.exp_ne_zero _) hconstant.ne',
        Real.log_exp, Real.log_exp]
      ring
end Ehrhart.BergmanJetLocalEnvelopeGrowth
