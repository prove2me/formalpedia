-- Prove2me | solution 1 for Ehrhart.WeightedTorusGraphWeakBridge.complexTorusCoverLift_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/fbb9c3b4-5f9f-47bb-8231-c85e1104a2bc

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_logarithmicCoordinates_measurePreserving
import Theorems.Thm_Ehrhart_WeightedTorusGraphWeakBridge_realTorusCoverLift_ae_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusGraphWeakBridge
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge
open WeightedTorusDistributionBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
namespace Ehrhart.WeightedTorusGraphWeakBridge
theorem _root_.solution {n : ℕ}
    {f g : WeightedTorusHilbert.LogTorus n → ℂ}
    (h : f =ᵐ[unweightedTorusMeasure n] g) :
    complexTorusCoverLift f =ᵐ[
      (volume : Measure (TorusCharacters.LogSpace n))]
      complexTorusCoverLift g := by
  have hr := realTorusCoverLift_ae_eq h
  have hp :=
    ((logarithmicCoordinates_measurePreserving n).symm
      (logarithmicCoordinatesEquiv n).toHomeomorph.toMeasurableEquiv).quasiMeasurePreserving.ae_eq_comp
        hr
  change
    (fun z : TorusCharacters.LogSpace n =>
      realTorusCoverLift f ((logarithmicCoordinatesEquiv n).symm z)) =ᵐ[
        logarithmicCoverPushforward n]
      (fun z : TorusCharacters.LogSpace n =>
        realTorusCoverLift g ((logarithmicCoordinatesEquiv n).symm z))
    at hp
  rw [logarithmicCoverPushforward_eq_smul_volume] at hp
  have hc : logarithmicCoverJacobianFactor n ≠ 0 :=
    (logarithmicCoverJacobianFactor_pos n).ne'
  have hv := (Measure.ae_smul_measure_iff hc).mp hp
  filter_upwards [hv] with z hz
  change
    f (realTorusCoverProjection n
      ((logarithmicCoordinatesEquiv n).symm z)) =
    g (realTorusCoverProjection n
      ((logarithmicCoordinatesEquiv n).symm z))
  exact hz
end Ehrhart.WeightedTorusGraphWeakBridge
