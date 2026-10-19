-- Prove2me | solution 1 for Ehrhart.MatrixTorusCompactGreen.angularScalarFundamentalLiftLI_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/1a6c53d8-9666-4c6d-be5a-5129ce6f6d46

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusCompactGreen
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerBridge
open WeightedTorusDolbeault TorusWeightedBaseAE
open scoped BigOperators ENNReal InnerProductSpace Topology
  MatrixOrder ComplexOrder ComplexConjugate ContDiff
namespace Ehrhart.MatrixTorusCompactGreen
theorem _root_.solution {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n) (f : angularWeightedScalarL2 a) :
    (fun p : Space n × Space n =>
      angularScalarFundamentalLiftLI ha b f p)
        =ᵐ[realAngularWeightedFundamentalCellMeasure a b]
      (fun p => f (realTorusCoverProjection n p)) := by
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving f
    (realAngularWeightedFundamentalCell_measurePreserving ha b)
end Ehrhart.MatrixTorusCompactGreen
