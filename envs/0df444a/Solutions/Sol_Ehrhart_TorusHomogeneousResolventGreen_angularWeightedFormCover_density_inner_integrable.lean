-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousResolventGreen.angularWeightedFormCover_density_inner_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/ada7a168-a6d3-4815-b622-77a305980b49

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_continuous_coverWeight
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_compactSupport_barPartialCoordinate
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
    (ha : Continuous a) (W : angularWeightedFormL2 a)
    {ψ : LogSpace n → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hψcompact : HasCompactSupport ψ) :
    Integrable
      (fun z : LogSpace n =>
        complexCoverWeight (angularCoverPotential a) z *
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n z))
            (WithLp.toLp 2
              (fun j : Fin n => barPartialCoordinate ψ z j)))
      (volume : Measure (LogSpace n)) := by
  have hd : Continuous
      (complexCoverWeight (angularCoverPotential a)) :=
    Complex.continuous_ofReal.comp
      (continuous_coverWeight (continuous_angularCoverPotential ha))
  have hj : ∀ j : Fin n, Integrable
      (fun z : LogSpace n =>
        complexCoverWeight (angularCoverPotential a) z *
          @inner ℂ ℂ _
            ((W (complexTorusCoverProjection n z) :
              EuclideanSpace ℂ (Fin n)) j)
            (barPartialCoordinate ψ z j))
      (volume : Measure (LogSpace n)) := by
    intro j
    have hG : Continuous
        (fun z : LogSpace n =>
          complexCoverWeight (angularCoverPotential a) z *
            barPartialCoordinate ψ z j) :=
      hd.mul (continuous_barPartialCoordinate hψ j)
    have hGc : HasCompactSupport
        (fun z : LogSpace n =>
          complexCoverWeight (angularCoverPotential a) z *
            barPartialCoordinate ψ z j) :=
      (compactSupport_barPartialCoordinate hψcompact j).mul_left
    have h := locallyIntegrable_complex_inner_mul_integrable
      (angularWeightedFormCoordinateCoverLift_locallyIntegrable
        ha W j) hG hGc
    simpa [complexTorusCoverLift, RCLike.inner_apply', mul_assoc,
      mul_left_comm, mul_comm] using h
  have hsum := integrable_finsetSum
    (Finset.univ : Finset (Fin n)) (fun j _ => hj j)
  simpa [PiLp.inner_apply, Finset.mul_sum] using hsum
end Ehrhart.TorusHomogeneousResolventGreen
