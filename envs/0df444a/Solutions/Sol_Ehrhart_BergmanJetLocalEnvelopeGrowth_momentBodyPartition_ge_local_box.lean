-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalEnvelopeGrowth.momentBodyPartition_ge_local_box
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/6e151c81-2446-4d75-bf4a-f4415dcbcef4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_measurableSet_sourceLocalTorusBox
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourceLocalBoxRadius_le_one
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourceTorusCoverPoint_mem_shrinkingBall_of_mem_box
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourceLocalTorusBox_realVolume_at_time
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourceLocalTorusBox_measure_ne_top
import Theorems.Thm_Ehrhart_BergmanJetLocalEnvelopeGrowth_momentTorusEnvelopeTimeSlice_local_le_maximum

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
    Real.exp
        (-momentLocalPotentialMaximum K
          (momentBodyOptimizer K) (0 : LogSpace n) R) *
      sourceLocalBallVolumeConstant n R *
        Real.exp (-(n : ℝ) * t) ≤
          momentBodyPartition K (0 : LogSpace n) t := by
  let A : Set (LogTorus n) :=
    sourceLocalTorusBox n (sourceLocalBoxRadius R t)
  have hA : MeasurableSet A :=
    measurableSet_sourceLocalTorusBox n (sourceLocalBoxRadius R t)
  have hAfinite : sourceTorusBaseMeasure n A ≠ ⊤ :=
    sourceLocalTorusBox_measure_ne_top n
      (sourceLocalBoxRadius_le_one hR ht.le)
  have hconst : IntegrableOn
      (fun _ : LogTorus n =>
        Real.exp
          (-momentLocalPotentialMaximum K
            (momentBodyOptimizer K) (0 : LogSpace n) R))
      A (sourceTorusBaseMeasure n) :=
    MeasureTheory.integrableOn_const hAfinite
  have hdensity := integrable_exp_neg_momentBodyTorusWeight
    K (0 : LogSpace n) t
  have hpoint : ∀ q ∈ A,
      Real.exp
        (-momentLocalPotentialMaximum K
          (momentBodyOptimizer K) (0 : LogSpace n) R) ≤
        Real.exp (-momentBodyTorusWeight
          K (0 : LogSpace n) t q) := by
    intro q hq
    have hcover := sourceTorusCoverPoint_mem_shrinkingBall_of_mem_box
      hR q hq
    have hlocal := momentTorusEnvelopeTimeSlice_local_le_maximum
      K (momentBodyOptimizer K)
      (momentBodyOptimizer_transport K)
      (0 : LogSpace n) q R t hR ht hcover
    unfold momentBodyTorusWeight
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    Real.exp
        (-momentLocalPotentialMaximum K
          (momentBodyOptimizer K) (0 : LogSpace n) R) *
      sourceLocalBallVolumeConstant n R *
        Real.exp (-(n : ℝ) * t) =
          ∫ _q : LogTorus n in A,
            Real.exp
              (-momentLocalPotentialMaximum K
                (momentBodyOptimizer K) (0 : LogSpace n) R)
              ∂(sourceTorusBaseMeasure n) := by
            rw [MeasureTheory.setIntegral_const]
            dsimp [A]
            rw [sourceLocalTorusBox_realVolume_at_time n hR ht.le]
            ring
    _ ≤ ∫ q : LogTorus n in A,
        Real.exp (-momentBodyTorusWeight
          K (0 : LogSpace n) t q)
          ∂(sourceTorusBaseMeasure n) :=
      setIntegral_mono_on hconst hdensity.integrableOn hA hpoint
    _ ≤ ∫ q : LogTorus n,
        Real.exp (-momentBodyTorusWeight
          K (0 : LogSpace n) t q)
          ∂(sourceTorusBaseMeasure n) := by
      apply setIntegral_le_integral hdensity
      exact Filter.Eventually.of_forall fun q =>
        (Real.exp_pos
          (-momentBodyTorusWeight
            K (0 : LogSpace n) t q)).le
    _ = momentBodyPartition K (0 : LogSpace n) t := by
      rfl
end Ehrhart.BergmanJetLocalEnvelopeGrowth
