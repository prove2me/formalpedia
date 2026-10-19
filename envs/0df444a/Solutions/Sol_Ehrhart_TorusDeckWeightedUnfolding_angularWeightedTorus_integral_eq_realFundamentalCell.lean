-- Prove2me | solution 1 for Ehrhart.TorusDeckWeightedUnfolding.angularWeightedTorus_integral_eq_realFundamentalCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/d111e7fb-8480-4e38-8951-9099ee4d7336

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusBochner_integral_angularUnweightedTorusIntegrand_eq_weighted

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusDeckWeightedUnfolding
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open WeightedTorusDistributionBridge WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault
open WeightedTorusBochner TorusWeightedBaseAE
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold
namespace Ehrhart.TorusDeckWeightedUnfolding
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (b : Space n)
    {G : LogTorus n → ℂ}
    (hG : AEStronglyMeasurable G (sourceTorusBaseMeasure n)) :
    (∫ q : LogTorus n, G q ∂(angularWeightedTorusMeasure a)) =
      ∫ p : Space n × Space n,
        angularUnweightedTorusIntegrand a G
          (realTorusCoverProjection n p)
        ∂(realFundamentalCellMeasure b) := by
  let H : LogTorus n → ℂ :=
    angularUnweightedTorusIntegrand a G
  have hH : AEStronglyMeasurable H (sourceTorusBaseMeasure n) := by
    exact ((Complex.continuous_ofReal.comp
      (continuous_angularWeightedTorusDensity ha)).aestronglyMeasurable).mul
      hG
  have hp := realTorusCoverProjection_measurePreserving
    (volume : Measure (Space n)) b
  have hmap :
      Measure.map (realTorusCoverProjection n)
        (realFundamentalCellMeasure b) =
        sourceTorusBaseMeasure n := by
    simpa [realFundamentalCellMeasure, sourceTorusBaseMeasure]
      using hp.map_eq
  calc
    (∫ q : LogTorus n, G q ∂(angularWeightedTorusMeasure a)) =
      ∫ q : LogTorus n, H q
        ∂(sourceTorusBaseMeasure n) :=
      (integral_angularUnweightedTorusIntegrand_eq_weighted ha G).symm
    _ = ∫ q : LogTorus n, H q
        ∂(Measure.map (realTorusCoverProjection n)
          (realFundamentalCellMeasure b)) := by rw [hmap]
    _ = ∫ p : Space n × Space n,
        H (realTorusCoverProjection n p)
        ∂(realFundamentalCellMeasure b) := by
      apply MeasureTheory.integral_map
        hp.measurable.aemeasurable
      rw [hmap]
      exact hH
end Ehrhart.TorusDeckWeightedUnfolding
