-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.realFundamentalCell_integral_eq_coverJacobian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/09b6f120-d153-4fe1-a3c2-74981b6f8a78

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_integral_logarithmicCoordinates_eq_jacobian
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_realFundamentalCellMeasure_eq_restrict

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusClosedGraphWeakBridge
open Set Function MeasureTheory Filter
open WeightedTorusHilbert WeightedBrascampSaturation ComplexKillingSaturationBridge
open DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
  Manifold ContDiff
namespace Ehrhart.WeightedTorusClosedGraphWeakBridge
theorem _root_.solution {n : ℕ}
    (b : Space n)
    (g : TorusCharacters.LogSpace n → ℂ)
    (hsupport : ∀ p : Space n × Space n,
      p.2 ∉ angularFundamentalBox b →
        g (logarithmicCoordinatesEquiv n p) = 0) :
    (∫ p : Space n × Space n,
      g (logarithmicCoordinatesEquiv n p)
      ∂(realFundamentalCellMeasure b)) =
      logarithmicCoverJacobianFactor n •
        (∫ z : TorusCharacters.LogSpace n, g z
          ∂(volume : Measure
            (TorusCharacters.LogSpace n))) := by
  calc
    _ = ∫ p : Space n × Space n,
        g (logarithmicCoordinatesEquiv n p)
        ∂(volume : Measure (Space n × Space n)) := by
      rw [realFundamentalCellMeasure_eq_restrict b]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      apply hsupport p
      simpa using hp
    _ = ∫ p : Space n × Space n,
        g (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
          p.1 p.2)
        ∂(volume : Measure (Space n × Space n)) := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun p =>
        congrArg g (logarithmicCoordinatesEquiv_apply p.1 p.2)
    _ = _ := integral_logarithmicCoordinates_eq_jacobian g
end Ehrhart.WeightedTorusClosedGraphWeakBridge
