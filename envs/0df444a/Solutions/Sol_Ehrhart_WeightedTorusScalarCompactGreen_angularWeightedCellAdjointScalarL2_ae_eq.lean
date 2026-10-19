-- Prove2me | solution 1 for Ehrhart.WeightedTorusScalarCompactGreen.angularWeightedCellAdjointScalarL2_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/ac348768-685c-4cbe-8c56-5537fd7cae26

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusScalarCompactGreen
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault
open TorusWeakDolbeaultMollification TorusMollifiedBochner BergmanJetStrictMixedLocalCore
open MatrixTorusCompactGreen
open scoped BigOperators ENNReal InnerProductSpace Topology
  ComplexConjugate ContDiff Convolution Manifold
namespace Ehrhart.WeightedTorusScalarCompactGreen
theorem _root_.solution {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    (fun p : Space n × Space n =>
      angularWeightedCellAdjointScalarL2 ha b hψ hψcompact j p)
      =ᵐ[realAngularWeightedFundamentalCellMeasure a b]
        angularWeightedCellAdjointScalarTest a ψ j := by
  let : IsLocallyFiniteMeasure
      (realAngularWeightedFundamentalCellMeasure a b) :=
    realAngularWeightedFundamentalCellMeasure_isLocallyFinite ha b
  simpa only [angularWeightedCellAdjointScalarL2] using
    (MeasureTheory.MemLp.coeFn_toLp
      ((continuous_angularWeightedCellAdjointScalarTest
        ha hψ j).memLp_of_hasCompactSupport
        (μ := realAngularWeightedFundamentalCellMeasure a b)
        (compactSupport_angularWeightedCellAdjointScalarTest
          a hψcompact j)))
end Ehrhart.WeightedTorusScalarCompactGreen
