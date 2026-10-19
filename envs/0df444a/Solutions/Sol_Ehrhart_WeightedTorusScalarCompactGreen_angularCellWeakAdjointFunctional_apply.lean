-- Prove2me | solution 1 for Ehrhart.WeightedTorusScalarCompactGreen.angularCellWeakAdjointFunctional_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/de545f90-186f-403f-a5e9-9eb85a72de13

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
    (hψcompact : HasCompactSupport ψ) (j : Fin n)
    (v : angularDolbeaultGraphAmbient a) :
    angularCellWeakAdjointFunctional ha b hψ hψcompact j v =
      @inner ℂ (angularWeightedCellScalarL2 a b) _
        (angularWeightedCellAdjointScalarL2 ha b hψ hψcompact j)
        (angularScalarFundamentalLiftLI ha b (WithLp.fst v)) +
      @inner ℂ (angularWeightedCellFormL2 a b) _
        (angularWeightedCellAdjointVectorL2 ha b hψ hψcompact j)
        (angularFormFundamentalLiftLI ha b (WithLp.snd v)) := by
  rfl
end Ehrhart.WeightedTorusScalarCompactGreen
