-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeGibbsBridge.eventually_integral_momentTorusJetSlope_Bergman_ge_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/d2d6bc5e-849e-4716-bc4f-61d6707a145e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusSlopeBridge_eventually_integral_momentPositiveTorusJetSlope_ge_sharp

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetTorusRightSlopeGibbsBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentRegularity
open BergmanJetTorusEnvelope BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge
open BergmanJetTorusRightSlopeBridge
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetTorusRightSlopeGibbsBridge
theorem _root_.solution
    {n : ℕ} (hn : 0 < n) (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      (n : ℝ) * BodyScale.canonicalScale K /
          ((n : ℝ) + 1) - ε ≤
        ∫ q : LogTorus n,
          momentTorusJetSlope K F htransport p k q
            ∂(momentTorusBergmanProbability K F k) := by
  filter_upwards
    [eventually_integral_momentPositiveTorusJetSlope_ge_sharp
      hn K F htransport p hε,
      eventually_gt_atTop (0 : ℕ)] with k hprofile hk
  simpa only [momentTorusJetSlope, dif_pos hk]
    using hprofile hk
end Ehrhart.BergmanJetTorusRightSlopeGibbsBridge
