-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousResolventGreen.angularWeightedScalarCover_density_inner_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/6863fe39-22b0-4371-bb7e-ed4f1e145152

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_continuous_coverWeight
import Theorems.Thm_Ehrhart_WeightedTorusDolbeault_continuous_angularCoverPotential
import Theorems.Thm_Ehrhart_TorusWeightedCoverGlobalGreen_locallyIntegrable_complex_inner_mul_integrable

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousResolventGreen
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert
open WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge
open WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault WeightedTorusBrascampLieb
open TorusDeckWeightedUnfolding TorusWeightedCoverAdjointGreen TorusWeightedCoverGlobalGreen
open BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold
namespace Ehrhart.TorusHomogeneousResolventGreen
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (f : angularWeightedScalarL2 a)
    {ψ : LogSpace n → ℂ}
    (hψ : Continuous ψ) (hψcompact : HasCompactSupport ψ) :
    Integrable
      (fun z : LogSpace n =>
        complexCoverWeight (angularCoverPotential a) z *
          @inner ℂ ℂ _
            (f (complexTorusCoverProjection n z)) (ψ z))
      (volume : Measure (LogSpace n)) := by
  have hd : Continuous
      (complexCoverWeight (angularCoverPotential a)) :=
    Complex.continuous_ofReal.comp
      (continuous_coverWeight (continuous_angularCoverPotential ha))
  have hG : Continuous
      (fun z : LogSpace n =>
        complexCoverWeight (angularCoverPotential a) z * ψ z) :=
    hd.mul hψ
  have hGc : HasCompactSupport
      (fun z : LogSpace n =>
        complexCoverWeight (angularCoverPotential a) z * ψ z) :=
    hψcompact.mul_left
  have h := locallyIntegrable_complex_inner_mul_integrable
    (angularWeightedScalarCoverLift_locallyIntegrable ha f) hG hGc
  simpa [complexTorusCoverLift, RCLike.inner_apply', mul_assoc,
    mul_left_comm, mul_comm] using h
end Ehrhart.TorusHomogeneousResolventGreen
