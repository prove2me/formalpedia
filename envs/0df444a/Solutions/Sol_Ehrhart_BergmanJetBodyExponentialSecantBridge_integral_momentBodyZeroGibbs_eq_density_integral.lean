-- Prove2me | solution 1 for Ehrhart.BergmanJetBodyExponentialSecantBridge.integral_momentBodyZeroGibbs_eq_density_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/51fb8db4-d79e-4d0f-9f05-e91a0f586094

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPartitionEndpoint_measurable_momentBodyTorusWeight

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
    (p : LogSpace n) (f : LogTorus n → ℝ) :
    (∫ q : LogTorus n, f q
      ∂(sourceProbability (momentBodyTorusWeight K p) 0)) =
      ∫ q : LogTorus n,
        f q * sourceNormalizedDensity
          (momentBodyTorusWeight K p) 0 q
        ∂(sourceTorusBaseMeasure n) := by
  let d : LogTorus n → ℝ≥0∞ := fun q =>
    ENNReal.ofReal
      (sourceNormalizedDensity (momentBodyTorusWeight K p) 0 q)
  have hdmeas : Measurable d := by
    apply ENNReal.measurable_ofReal.comp
    unfold sourceNormalizedDensity sourceTimeDensity
    exact ((Real.continuous_exp.measurable.comp
      (measurable_momentBodyTorusWeight K p 0).neg).div_const
        (sourcePartition (momentBodyTorusWeight K p) 0))
  have hfinite : ∀ᵐ q ∂(sourceTorusBaseMeasure n), d q < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  unfold sourceProbability
  rw [integral_withDensity_eq_integral_toReal_smul hdmeas hfinite]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with q
  rw [ENNReal.toReal_ofReal
    (sourceNormalizedDensity_momentBody_pos K p 0 q).le]
  simp [smul_eq_mul, mul_comm]
end Ehrhart.BergmanJetBodyExponentialSecantBridge
