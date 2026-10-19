-- Prove2me | solution 1 for Ehrhart.MatrixTorusCompactGreen.angularWeightedCellAdjointVectorL2_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/990e8ebc-a172-41d6-80aa-244009a77600

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
    (b : Space n) {ψ : LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    (fun p : Space n × Space n =>
      angularWeightedCellAdjointVectorL2 ha b hψ hψcompact j p)
        =ᵐ[realAngularWeightedFundamentalCellMeasure a b]
      angularWeightedCellAdjointVectorTest a ψ j := by
  let : IsLocallyFiniteMeasure
      (realAngularWeightedFundamentalCellMeasure a b) :=
    realAngularWeightedFundamentalCellMeasure_isLocallyFinite ha b
  simpa only [angularWeightedCellAdjointVectorL2] using
    (MeasureTheory.MemLp.coeFn_toLp
      ((continuous_angularWeightedCellAdjointVectorTest
        ha hψ j).memLp_of_hasCompactSupport
        (μ := realAngularWeightedFundamentalCellMeasure a b)
        (compactSupport_angularWeightedCellAdjointVectorTest
          a hψcompact j)))
end Ehrhart.MatrixTorusCompactGreen
