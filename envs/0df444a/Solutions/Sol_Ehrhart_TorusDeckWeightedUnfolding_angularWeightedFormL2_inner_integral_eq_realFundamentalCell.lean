-- Prove2me | solution 1 for Ehrhart.TorusDeckWeightedUnfolding.angularWeightedFormL2_inner_integral_eq_realFundamentalCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/901b920b-0024-4b02-b473-432e5c343254

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusWeightedBaseAE_angularWeightedLp_aestronglyMeasurable_base
import Theorems.Thm_Ehrhart_TorusDeckWeightedUnfolding_angularWeightedTorus_integral_eq_realFundamentalCell

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
    (W : angularWeightedFormL2 a)
    {V : LogTorus n → EuclideanSpace ℂ (Fin n)}
    (hV : Continuous V) :
    (∫ q : LogTorus n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _ (W q) (V q)
        ∂(angularWeightedTorusMeasure a)) =
      ∫ p : Space n × Space n,
        angularUnweightedTorusIntegrand a
          (fun q : LogTorus n =>
            @inner ℂ (EuclideanSpace ℂ (Fin n)) _ (W q) (V q))
          (realTorusCoverProjection n p)
        ∂(realFundamentalCellMeasure b) := by
  apply angularWeightedTorus_integral_eq_realFundamentalCell ha b
  exact (angularWeightedLp_aestronglyMeasurable_base W).inner
    hV.aestronglyMeasurable
end Ehrhart.TorusDeckWeightedUnfolding
