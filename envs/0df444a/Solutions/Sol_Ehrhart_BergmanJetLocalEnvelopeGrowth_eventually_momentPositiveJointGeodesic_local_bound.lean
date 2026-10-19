-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalEnvelopeGrowth.eventually_momentPositiveJointGeodesic_local_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:24.337506+00:00
-- url     : https://prove2.me/submissions/77331406-eb19-4747-b3ee-e9a989f3d619

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetLocalGrowth_eventually_momentJetGeodesic_local_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetLocalEnvelopeGrowth
open Set Function Filter MeasureTheory Module Metric
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open BergmanJetUpperEnvelope BergmanJetEnvelopeLimit BergmanJetTorusEnvelope
open BergmanJetPartitionEndpoint BergmanJetLocalGrowth ActualJetUpperEnvelope
open JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative JetEnvelopeLocalGrowth
open LogPartitionConvexity
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetLocalEnvelopeGrowth
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (R : ℝ) (hR : 0 < R) :
    ∀ᶠ k : ℕ in atTop, ∀ w ∈ sourceLocalJointRegion p R,
      momentPositiveJointGeodesic K F htransport p k w ≤
        momentLocalPotentialMaximum K F p R +
          sourceLocalKernelLogError K (k + 1) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_momentJetGeodesic_local_bound
      K F htransport p R hR)
  filter_upwards [eventually_ge_atTop N] with k hk w hw
  rw [momentPositiveJointGeodesic_eq_momentJetGeodesic]
  exact hN (k + 1) (by omega) (Nat.zero_lt_succ k)
    (Nat.floor (BodyScale.canonicalScale K *
      ((k + 1 : ℕ) : ℝ))) w.val.1 (jointLogTime w)
    (jointLogTime_pos w).le hw
end Ehrhart.BergmanJetLocalEnvelopeGrowth
