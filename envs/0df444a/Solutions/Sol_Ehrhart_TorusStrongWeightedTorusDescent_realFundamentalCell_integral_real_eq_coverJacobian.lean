-- Prove2me | solution 1 for Ehrhart.TorusStrongWeightedTorusDescent.realFundamentalCell_integral_real_eq_coverJacobian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/802ab861-3592-49f4-9444-8af3b3c1ae66

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_logarithmicCoordinates_measurePreserving
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_realFundamentalCellMeasure_eq_restrict

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusStrongWeightedTorusDescent
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open JointHolomorphicLaurentFourierCompatibility ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault TorusWeightedCoverAdjointGreen
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusStrongWeightedTorusDescent
theorem _root_.solution
    {n : ℕ} (b : Space n)
    (g : LogSpace n → ℝ)
    (hsupport : ∀ p : Space n × Space n,
      p.2 ∉ angularFundamentalBox b →
        g (logarithmicCoordinatesEquiv n p) = 0) :
    (∫ p : Space n × Space n,
      g (logarithmicCoordinatesEquiv n p)
        ∂(realFundamentalCellMeasure b)) =
      logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n, g z
          ∂(volume : Measure (LogSpace n))) := by
  calc
    _ = ∫ p : Space n × Space n,
        g (logarithmicCoordinatesEquiv n p)
          ∂(volume : Measure
            (Space n × Space n)) := by
      rw [realFundamentalCellMeasure_eq_restrict b]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      apply hsupport p
      simpa using hp
    _ = ∫ z : LogSpace n, g z
          ∂(logarithmicCoverPushforward n) := by
      simpa [Function.comp_def, logarithmicCoordinatesEquiv_apply] using
        (logarithmicCoordinates_measurePreserving n).integral_comp
          (logarithmicCoordinatesEquiv n).toHomeomorph.measurableEmbedding g
    _ = _ := by
      rw [logarithmicCoverPushforward_eq_smul_volume,
        integral_smul_nnreal_measure]
end Ehrhart.TorusStrongWeightedTorusDescent
