-- Prove2me | solution 1 for Ehrhart.BergmanJetBodyExponentialSecantBridge.integral_momentBodyEnvelopeRelativeDensity_eq_normalizedPartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/809f8ef2-d4ac-4d65-b0d4-bff60517f7e6

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetBodyExponentialSecantBridge_integral_momentBodyZeroGibbs_eq_density_integral

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetBodyExponentialSecantBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity
open BergmanJetPartitionEndpoint BergmanJetTorusRightSlopeGibbsBridge
open BergmanJetBodyLogPartitionSharpGrowth
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetBodyExponentialSecantBridge
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    (∫ q : LogTorus n,
      momentBodyEnvelopeRelativeDensity K p t q
        ∂(sourceProbability (momentBodyTorusWeight K p) 0)) =
      momentBodyNormalizedPartition K p t := by
  rw [integral_momentBodyZeroGibbs_eq_density_integral]
  unfold momentBodyEnvelopeRelativeDensity
    sourceNormalizedDensity sourceTimeDensity
    momentBodyNormalizedPartition
  change
    (∫ q : LogTorus n,
      Real.exp
        (-(momentBodyTorusWeight K p t q -
          momentBodyTorusWeight K p 0 q)) *
        (Real.exp (-momentBodyTorusWeight K p 0 q) /
          momentBodyPartition K p 0)
      ∂(sourceTorusBaseMeasure n)) =
      momentBodyPartition K p t /
        normalizedVolume K.carrier
  rw [momentBodyPartition_zero,
    momentBodyPartition_eq_integral,
    ← MeasureTheory.integral_div]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with q
  rw [← mul_div_assoc, ← Real.exp_add]
  congr 2
  ring
end Ehrhart.BergmanJetBodyExponentialSecantBridge
