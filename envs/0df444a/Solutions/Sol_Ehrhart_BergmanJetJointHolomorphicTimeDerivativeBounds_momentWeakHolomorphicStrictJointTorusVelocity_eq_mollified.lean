-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.momentWeakHolomorphicStrictJointTorusVelocity_eq_mollified
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/3f97f126-1649-46f4-a6a6-a799a560798d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_EnvelopeGeneralTorusDescent_hasDerivAt_jointSourceTorusWeight

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert MatrixTorusBochnerBridge MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation BergmanJetEnvelopePlurisubharmonic
open BergmanJetUpperEnvelope BergmanJetStrictRadialRegularizer BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetJointHolomorphicStrictSchur
open ActualJetUpperEnvelope JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative
open JetEnvelopeTrueRadialMollifier EnvelopeSmoothing EnvelopeGeneralTorusDescent
open RadialAccelerationBounds
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder
attribute [local instance] Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.sourceJointCoverVolume_isAddHaar
namespace Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (q : LogTorus n) :
    jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q =
      (1 - ε) *
        jointSourceTorusVelocity
          (momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k) t q := by
  let M : SourceJointComplexCover n → ℝ :=
    momentWeakHolomorphicJointTrueRadialMollification
      K F htransport p k
  let G : SourceJointComplexCover n → ℝ :=
    momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k
  have hM : ContDiff ℝ 2 M := by
    dsimp [M]
    exact (contDiff_infty.mp
      (contDiff_momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k)) 2
  have hG : ContDiff ℝ 2 G := by
    dsimp [G]
    exact (contDiff_infty.mp
      (contDiff_momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)) 2
  have hraw := hasDerivAt_jointSourceTorusWeight hM t q
  have hscaled : HasDerivAt
      (fun u : ℝ =>
        (1 - ε) * jointSourceTorusWeight M u q +
          ε * matrixSourceCoverPotential
            (momentBodyStrictRadialPotential K)
              (sourceTorusCoverPoint q))
      ((1 - ε) * jointSourceTorusVelocity M t q) t :=
    (hraw.const_mul (1 - ε)).add_const
      (ε * matrixSourceCoverPotential
        (momentBodyStrictRadialPotential K)
          (sourceTorusCoverPoint q))
  have heq :
      (fun u : ℝ => jointSourceTorusWeight G u q) =
      (fun u : ℝ =>
        (1 - ε) * jointSourceTorusWeight M u q +
          ε * matrixSourceCoverPotential
            (momentBodyStrictRadialPotential K)
              (sourceTorusCoverPoint q)) := by
    funext u
    rw [jointSourceTorusWeight_eq_cover,
      jointSourceTorusWeight_eq_cover]
    rfl
  have hderived : HasDerivAt
      (fun u : ℝ => jointSourceTorusWeight G u q)
      ((1 - ε) * jointSourceTorusVelocity M t q) t := by
    rw [heq]
    exact hscaled
  have huniq :=
    (hasDerivAt_jointSourceTorusWeight hG t q).unique hderived
  exact huniq
end Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
