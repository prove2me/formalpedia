-- Prove2me | solution 1 for Ehrhart.TorusWeightedCoverAdjointGreen.angularWeakDolbeaultResolvent_weighted_cover_green_of_fundamentalInterior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/50b8341a-6947-4548-9df2-9e5aff9c1977

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusDeckGraphAdjoint_angularWeakDolbeaultResolvent_complexDeckPeriodization_adjoint_integral
import Theorems.Thm_Ehrhart_TorusWeightedCoverAdjointGreen_angularWeightedScalarL2_periodized_cell_inner_eq_cover
import Theorems.Thm_Ehrhart_TorusWeightedCoverAdjointGreen_angularWeightedFormL2_periodized_cell_inner_eq_cover

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeightedCoverAdjointGreen
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert
open JointHolomorphicLaurentFourierCompatibility ComplexKillingSaturationBridge
open WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault WeightedTorusBochner WeightedTorusBrascampLieb TorusDeckPeriodization
open TorusDeckGraphAdjoint TorusDeckFundamentalCell TorusDeckFullCellDerivative
open TorusDeckWeightedUnfolding
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold
namespace Ehrhart.TorusWeightedCoverAdjointGreen
theorem _root_.solution
    {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (b : Space n)
    (f : angularWeightedScalarL2 a)
    {ψ : LogSpace n → ℂ}
    (hψ : ContDiff ℝ 3 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalInterior b) :
    (∫ z : LogSpace n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        ((WithLp.snd
          (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a))
              (complexTorusCoverProjection n z))
        (WithLp.toLp 2
          (fun j : Fin n => barPartialCoordinate ψ z j))
      ∂(coverWeightedMeasure (angularCoverPotential a))) =
    (∫ z : LogSpace n,
      @inner ℂ ℂ _
        ((f - angularWeakScalarResolventCLM a f)
          (complexTorusCoverProjection n z))
        (ψ z)
      ∂(coverWeightedMeasure (angularCoverPotential a))) := by
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a)
  let r : angularWeightedScalarL2 a :=
    f - angularWeakScalarResolventCLM a f
  have hform := angularWeightedFormL2_periodized_cell_inner_eq_cover
    ha b W hψ hψcompact hcell
  have hscalar := angularWeightedScalarL2_periodized_cell_inner_eq_cover
    ha b r hψ hψcompact hcell
  have htorus :=
    angularWeakDolbeaultResolvent_complexDeckPeriodization_adjoint_integral
      ha f hψ hψcompact
  change
    (∫ q : LogTorus n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (W q)
        (torusFunctionBarPartialRepresentative
          (complexDeckPeriodization ψ) q)
      ∂(angularWeightedTorusMeasure a)) =
    (∫ q : LogTorus n,
      @inner ℂ ℂ _
        (r q)
        (torusScalarRepresentative
          (complexDeckPeriodization ψ) q)
      ∂(angularWeightedTorusMeasure a)) at htorus
  rw [hform, hscalar] at htorus
  have hzero :
      logarithmicCoverJacobianFactor n •
        ((∫ z : LogSpace n,
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n z))
            (WithLp.toLp 2
              (fun j : Fin n => barPartialCoordinate ψ z j))
          ∂(coverWeightedMeasure (angularCoverPotential a))) -
          (∫ z : LogSpace n,
            @inner ℂ ℂ _
              (r (complexTorusCoverProjection n z))
              (ψ z)
            ∂(coverWeightedMeasure (angularCoverPotential a)))) = 0 := by
    rw [smul_sub, htorus, sub_self]
  have hcover :
      (∫ z : LogSpace n,
        @inner ℂ (EuclideanSpace ℂ (Fin n)) _
          (W (complexTorusCoverProjection n z))
          (WithLp.toLp 2
            (fun j : Fin n => barPartialCoordinate ψ z j))
        ∂(coverWeightedMeasure (angularCoverPotential a))) =
      (∫ z : LogSpace n,
        @inner ℂ ℂ _
          (r (complexTorusCoverProjection n z))
          (ψ z)
        ∂(coverWeightedMeasure (angularCoverPotential a))) := by
    apply sub_eq_zero.mp
    exact (smul_eq_zero.mp hzero).resolve_left
      (logarithmicCoverJacobianFactor_pos n).ne'
  exact hcover
end Ehrhart.TorusWeightedCoverAdjointGreen
