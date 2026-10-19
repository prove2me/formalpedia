-- Prove2me | solution 1 for Ehrhart.BergmanJetBergmanProbabilityTransfer.momentWeakTorusGibbsDensity_body_eq_zeroTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/40be7efa-3ee9-4c45-9e68-474cc126845e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MomentWeakBergmanProbabilityEndpoint_momentNormalizedDensity_div_volume_eq_gibbsDensity

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetBergmanProbabilityTransfer
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert BergmanMonomials BergmanNormalization
open JetEnvelopeSlopeConvergence LogPartitionConvexity MomentOptimizer MomentWeakFirstVariation
open MomentRegularity MomentWeakBergman MomentWeakBergmanProbabilityEndpoint
open BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetBergmanProbabilityTransfer
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (q : LogTorus n) :
    momentWeakTorusGibbsDensity
      (momentBodyOptimizer K) q =
        sourceNormalizedDensity (momentBodyTorusWeight K p) 0 q := by
  unfold momentWeakTorusGibbsDensity
    sourceNormalizedDensity sourceTimeDensity
  rw [momentBodyTorusWeight_zero]
  change
    WeightedPoincare.normalizedDensity
      (momentBodyOptimizer K).potential q.1 =
      Real.exp
        (-momentNormalizedPotential (momentBodyOptimizer K) q.1) /
        momentBodyPartition K p 0
  rw [momentBodyPartition_zero]
  exact (momentNormalizedDensity_div_volume_eq_gibbsDensity
    (momentBodyOptimizer K) q.1).symm
end Ehrhart.BergmanJetBergmanProbabilityTransfer
