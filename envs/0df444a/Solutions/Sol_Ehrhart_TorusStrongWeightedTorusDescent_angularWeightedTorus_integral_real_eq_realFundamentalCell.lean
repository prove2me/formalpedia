-- Prove2me | solution 1 for Ehrhart.TorusStrongWeightedTorusDescent.angularWeightedTorus_integral_real_eq_realFundamentalCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/6672c84c-658f-4d7c-a7ca-d8f6fa7bc3bc

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDolbeault_angularWeightedTorusDensity_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusStrongWeightedTorusDescent
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open JointHolomorphicLaurentFourierCompatibility ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault TorusWeightedCoverAdjointGreen
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusStrongWeightedTorusDescent
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (b : Space n)
    {G : LogTorus n → ℝ}
    (hG : AEStronglyMeasurable G (sourceTorusBaseMeasure n)) :
    (∫ q : LogTorus n, G q
      ∂(angularWeightedTorusMeasure a)) =
      ∫ p : Space n × Space n,
        angularWeightedTorusDensity a
            (realTorusCoverProjection n p) *
          G (realTorusCoverProjection n p)
        ∂(realFundamentalCellMeasure b) := by
  have hd : Measurable
      (fun q : LogTorus n =>
        ENNReal.ofReal (angularWeightedTorusDensity a q)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_angularWeightedTorusDensity ha).measurable
  have hp := realTorusCoverProjection_measurePreserving
    (volume : Measure (Space n)) b
  have hmap :
      Measure.map (realTorusCoverProjection n)
        (realFundamentalCellMeasure b) =
        sourceTorusBaseMeasure n := by
    simpa [realFundamentalCellMeasure, sourceTorusBaseMeasure]
      using hp.map_eq
  rw [angularWeightedTorusMeasure,
    integral_withDensity_eq_integral_toReal_smul hd
      (Filter.Eventually.of_forall fun q => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal
    (angularWeightedTorusDensity_pos a _).le, smul_eq_mul]
  calc
    (∫ q : LogTorus n,
      angularWeightedTorusDensity a q * G q
        ∂(sourceTorusBaseMeasure n)) =
      ∫ q : LogTorus n,
        angularWeightedTorusDensity a q * G q
          ∂(Measure.map (realTorusCoverProjection n)
            (realFundamentalCellMeasure b)) := by rw [hmap]
    _ = _ := by
      apply MeasureTheory.integral_map
        hp.measurable.aemeasurable
      rw [hmap]
      exact (continuous_angularWeightedTorusDensity ha).aestronglyMeasurable.mul hG
end Ehrhart.TorusStrongWeightedTorusDescent
