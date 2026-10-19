-- Prove2me | solution 1 for Ehrhart.WeightedTorusDistributionBridge.integral_logarithmicCoordinates_eq_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/e848217f-775a-41b2-beaa-7c49c8979dd5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_integral_logarithmicCoordinates_eq_pushforward

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
      logarithmicCoverJacobianFactor n •
        (∫ z : TorusCharacters.LogSpace n, g z
          ∂(volume : Measure (TorusCharacters.LogSpace n))) := by
  rw [integral_logarithmicCoordinates_eq_pushforward,
    logarithmicCoverPushforward_eq_smul_volume,
    integral_smul_nnreal_measure]
end Ehrhart.WeightedTorusDistributionBridge
