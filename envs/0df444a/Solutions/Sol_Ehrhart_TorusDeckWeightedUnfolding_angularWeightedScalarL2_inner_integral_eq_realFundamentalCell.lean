-- Prove2me | solution 1 for Ehrhart.TorusDeckWeightedUnfolding.angularWeightedScalarL2_inner_integral_eq_realFundamentalCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/5888b963-2703-4fc9-91a5-9e2f7afbb8f5

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
    (f : angularWeightedScalarL2 a)
    {G : LogTorus n → ℂ}
    (hG : Continuous G) :
    (∫ q : LogTorus n,
      @inner ℂ ℂ _ (f q) (G q)
        ∂(angularWeightedTorusMeasure a)) =
      ∫ p : Space n × Space n,
        angularUnweightedTorusIntegrand a
          (fun q : LogTorus n => @inner ℂ ℂ _ (f q) (G q))
          (realTorusCoverProjection n p)
        ∂(realFundamentalCellMeasure b) := by
  apply angularWeightedTorus_integral_eq_realFundamentalCell ha b
  exact (angularWeightedLp_aestronglyMeasurable_base f).inner
    hG.aestronglyMeasurable
end Ehrhart.TorusDeckWeightedUnfolding
