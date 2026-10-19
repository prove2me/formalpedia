-- Prove2me | solution 1 for Ehrhart.WeightedTorusScalarCompactGreen.angularScalarGraphGenerator_complexCoverLift_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/1c378176-cdbd-493f-b95b-b30e65995228

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusCompactGreen_angularWeightedTorus_complexCoverLift_ae_eq

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
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (F : LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (imaginaryShift q))
    (hF : MemLp (torusScalarRepresentative F) 2
      (angularWeightedTorusMeasure a)) :
    complexTorusCoverLift
      (fun q : LogTorus n => angularScalarL2OfRepresentative a F hF q)
        =ᵐ[(volume : Measure (LogSpace n))] F := by
  have h := angularWeightedTorus_complexCoverLift_ae_eq
    ha hF.coeFn_toLp
  change
    complexTorusCoverLift
      (fun q : LogTorus n => angularScalarL2OfRepresentative a F hF q)
      =ᵐ[(volume : Measure (LogSpace n))]
        complexTorusCoverLift (torusScalarRepresentative F) at h
  simpa [complexTorusCoverLift_torusScalarRepresentative_eq
    F hperiod] using h
end Ehrhart.WeightedTorusScalarCompactGreen
