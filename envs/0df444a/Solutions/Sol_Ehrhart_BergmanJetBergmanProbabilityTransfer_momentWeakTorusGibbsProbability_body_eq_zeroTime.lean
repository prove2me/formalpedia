-- Prove2me | solution 1 for Ehrhart.BergmanJetBergmanProbabilityTransfer.momentWeakTorusGibbsProbability_body_eq_zeroTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/cd58c585-ddb3-469b-93d4-712d1278d59b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetBergmanProbabilityTransfer_momentWeakTorusGibbsProbability_eq_base_withDensity
import Theorems.Thm_Ehrhart_BergmanJetBergmanProbabilityTransfer_momentWeakTorusGibbsDensity_body_eq_zeroTime

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
    (p : LogSpace n) :
    momentWeakTorusGibbsProbability
      (momentBodyOptimizer K) =
        sourceProbability (momentBodyTorusWeight K p) 0 := by
  rw [momentWeakTorusGibbsProbability_eq_base_withDensity]
  unfold sourceProbability
  congr 1
  funext q
  rw [momentWeakTorusGibbsDensity_body_eq_zeroTime K p q]
end Ehrhart.BergmanJetBergmanProbabilityTransfer
