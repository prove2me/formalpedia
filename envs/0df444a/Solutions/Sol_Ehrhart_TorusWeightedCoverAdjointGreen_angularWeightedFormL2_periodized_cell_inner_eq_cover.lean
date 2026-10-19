-- Prove2me | solution 1 for Ehrhart.TorusWeightedCoverAdjointGreen.angularWeightedFormL2_periodized_cell_inner_eq_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/f91e8e23-7561-498a-81cf-c78d3f39a2dc

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_integral_coverWeightedMeasure
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_realFundamentalCell_integral_eq_coverJacobian
import Theorems.Thm_Ehrhart_WeightedTorusDolbeault_continuous_angularCoverPotential
import Theorems.Thm_Ehrhart_TorusDeckPeriodization_complexDeckPeriodization_periodic
import Theorems.Thm_Ehrhart_TorusDeckPeriodization_contDiff_complexDeckPeriodization
import Theorems.Thm_Ehrhart_TorusDeckWeightedUnfolding_angularWeightedFormL2_inner_integral_eq_realFundamentalCell
import Theorems.Thm_Ehrhart_TorusDeckFullCellDerivative_barPartial_complexDeckPeriodization_eq_on_fundamentalCell
import Theorems.Thm_Ehrhart_TorusWeightedCoverAdjointGreen_ae_mem_angularFundamentalBox_realFundamentalCell

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
    (W : angularWeightedFormL2 a)
    {ψ : LogSpace n → ℂ}
    (hψ : ContDiff ℝ 3 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalInterior b) :
    (∫ q : LogTorus n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (W q)
        (torusFunctionBarPartialRepresentative
          (complexDeckPeriodization ψ) q)
      ∂(angularWeightedTorusMeasure a)) =
      logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n,
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n z))
            (WithLp.toLp 2
              (fun j : Fin n => barPartialCoordinate ψ z j))
          ∂(coverWeightedMeasure (angularCoverPotential a))) := by
  let F : LogSpace n → ℂ := complexDeckPeriodization ψ
  let g : LogSpace n → ℂ := fun z =>
    complexCoverWeight (angularCoverPotential a) z *
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (W (complexTorusCoverProjection n z))
        (WithLp.toLp 2
          (fun j : Fin n => barPartialCoordinate ψ z j))
  have hFperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (imaginaryShift q) :=
    fun q => complexDeckPeriodization_periodic ψ q
  have hFcontinuous :
      Continuous (torusFunctionBarPartialRepresentative F) :=
    continuous_torusFunctionBarPartialRepresentative_of_periodic
      ((contDiff_complexDeckPeriodization hψ hψcompact).of_le
        (by norm_num)) hFperiod
  have hhalf : tsupport ψ ⊆
      {z : LogSpace n |
        ((logarithmicCoordinatesEquiv n).symm z).2 ∈
          angularFundamentalBox b} := by
    intro z hz i
    have hi := hcell hz i
    exact ⟨hi.1, hi.2.le⟩
  calc
    (∫ q : LogTorus n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (W q) (torusFunctionBarPartialRepresentative F q)
      ∂(angularWeightedTorusMeasure a)) =
      ∫ p : Space n × Space n,
        angularUnweightedTorusIntegrand a
          (fun q : LogTorus n =>
            @inner ℂ (EuclideanSpace ℂ (Fin n)) _
              (W q) (torusFunctionBarPartialRepresentative F q))
          (realTorusCoverProjection n p)
        ∂(realFundamentalCellMeasure b) :=
      angularWeightedFormL2_inner_integral_eq_realFundamentalCell
        ha b W hFcontinuous
    _ = ∫ p : Space n × Space n,
        g (logarithmicCoordinatesEquiv n p)
        ∂(realFundamentalCellMeasure b) := by
      apply integral_congr_ae
      filter_upwards
        [ae_mem_angularFundamentalBox_realFundamentalCell b]
        with p hp
      have hrow :
          torusFunctionBarPartialRepresentative F
            (realTorusCoverProjection n p) =
          WithLp.toLp 2
            (fun j : Fin n =>
              barPartialCoordinate ψ
                (logarithmicCoordinatesEquiv n p) j) := by
        ext j
        change
          torusScalarRepresentative
            (fun z : LogSpace n => barPartialCoordinate F z j)
            (p.1, angularCoverProjection n p.2) =
          barPartialCoordinate ψ
            (logarithmicCoordinatesEquiv n p) j
        rw [periodic_torusScalarRepresentative_logarithmicPoint
          (fun z : LogSpace n => barPartialCoordinate F z j)
          (fun q => barPartialCoordinate_periodic F hFperiod j q)
          p.1 p.2]
        change
          barPartialCoordinate (complexDeckPeriodization ψ)
            (logarithmicPoint p.1 p.2) j =
          barPartialCoordinate ψ
            (logarithmicPoint p.1 p.2) j
        exact barPartial_complexDeckPeriodization_eq_on_fundamentalCell
          hψcompact hcell p.1 p.2 hp j
      have hproj :
          complexTorusCoverProjection n
            (logarithmicCoordinatesEquiv n p) =
            realTorusCoverProjection n p := by
        change
          complexTorusCoverProjection n
            (logarithmicPoint p.1 p.2) =
            realTorusCoverProjection n (p.1, p.2)
        exact complexTorusCoverProjection_logarithmicPoint p.1 p.2
      change
        (angularWeightedTorusDensity a
          (realTorusCoverProjection n p) : ℂ) *
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (realTorusCoverProjection n p))
            (torusFunctionBarPartialRepresentative F
              (realTorusCoverProjection n p)) =
        complexCoverWeight (angularCoverPotential a)
          (logarithmicCoordinatesEquiv n p) *
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n
              (logarithmicCoordinatesEquiv n p)))
            (WithLp.toLp 2
              (fun j : Fin n =>
                barPartialCoordinate ψ
                  (logarithmicCoordinatesEquiv n p) j))
      rw [hrow, hproj]
      simp only [complexCoverWeight, coverWeight,
        angularCoverPotential, angularWeightedTorusDensity, hproj]
    _ = logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n, g z
          ∂(volume : Measure (LogSpace n))) := by
      apply realFundamentalCell_integral_eq_coverJacobian b g
      intro p hp
      have hz : logarithmicCoordinatesEquiv n p ∉ tsupport ψ := by
        intro hz
        apply hp
        have hh := hhalf hz
        change
          ((logarithmicCoordinatesEquiv n).symm
            (logarithmicCoordinatesEquiv n p)).2 ∈
            angularFundamentalBox b at hh
        simpa using hh
      have hzero :
          WithLp.toLp 2
            (fun j : Fin n =>
              barPartialCoordinate ψ
                (logarithmicCoordinatesEquiv n p) j) =
            (0 : EuclideanSpace ℂ (Fin n)) := by
        ext j
        unfold barPartialCoordinate
        rw [fderiv_of_notMem_tsupport ℝ hz]
        simp
      simp [g, hzero]
    _ = logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n,
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n z))
            (WithLp.toLp 2
              (fun j : Fin n => barPartialCoordinate ψ z j))
          ∂(coverWeightedMeasure (angularCoverPotential a))) := by
      congr 1
      exact
        (integral_coverWeightedMeasure
          (continuous_angularCoverPotential ha)
          (fun z : LogSpace n =>
            @inner ℂ (EuclideanSpace ℂ (Fin n)) _
              (W (complexTorusCoverProjection n z))
              (WithLp.toLp 2
                (fun j : Fin n => barPartialCoordinate ψ z j)))).symm
end Ehrhart.TorusWeightedCoverAdjointGreen
