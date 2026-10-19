-- Prove2me | solution 1 for Ehrhart.TorusWeightedCoverAdjointGreen.ae_mem_angularFundamentalBox_realFundamentalCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/e21ba2e6-5357-4d88-81fd-33cefed33b6c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_realFundamentalCellMeasure_eq_restrict
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_measurableSet_angularFundamentalBox

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
    (b : Space n) :
    ∀ᵐ p : Space n × Space n
      ∂(realFundamentalCellMeasure b),
      p.2 ∈ angularFundamentalBox b := by
  rw [realFundamentalCellMeasure_eq_restrict]
  filter_upwards
    [ae_restrict_mem
      (MeasurableSet.univ.prod
        (measurableSet_angularFundamentalBox b))]
    with p hp
  exact hp.2
end Ehrhart.TorusWeightedCoverAdjointGreen
