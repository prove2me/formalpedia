-- Prove2me | solution 1 for Ehrhart.WeightedTorusDistributionBridge.integral_logarithmicCoordinates_eq_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/497eb810-7813-4d86-9233-ca5a54a28bdd

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_logarithmicCoordinates_measurePreserving

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusDistributionBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
attribute [local instance] Ehrhart.WeightedTorusDistributionBridge._p2m_local_instance_3610026555_18903
attribute [local instance] Ehrhart.WeightedTorusDistributionBridge._p2m_local_instance_3610026555_18906
namespace Ehrhart.WeightedTorusDistributionBridge
theorem _root_.solution {n : ℕ}
    (g : TorusCharacters.LogSpace n → ℂ) :
    (∫ p : Space n × Space n,
      g (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        p.1 p.2)
      ∂(volume : Measure (Space n × Space n))) =
      ∫ z : TorusCharacters.LogSpace n, g z
        ∂(logarithmicCoverPushforward n) := by
  calc
    (∫ p : Space n × Space n,
      g (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        p.1 p.2)
      ∂(volume : Measure (Space n × Space n))) =
        ∫ p : Space n × Space n,
          g (logarithmicCoordinatesEquiv n p)
          ∂(volume : Measure (Space n × Space n)) := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun p =>
        congrArg g (logarithmicCoordinatesEquiv_apply p.1 p.2).symm
    _ = _ :=
      (logarithmicCoordinates_measurePreserving n).integral_comp
        (logarithmicCoordinatesEquiv n).toHomeomorph.measurableEmbedding g
end Ehrhart.WeightedTorusDistributionBridge
