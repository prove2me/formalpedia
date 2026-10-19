-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedZeroGraph_hasWeakBarPartialZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/b8a801e1-96ba-467f-8987-aee92df7f778

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_weightedScalarL2_complexTorusCoverLift_locallyIntegrable
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedZeroGraph_compact_barPartial_zero_of_fundamentalCell
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_coverTestWithinFundamentalCell_of_tsupport_subset_interior
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_exists_finite_fundamental_test_partition
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_coverBarPartialTest_finset_sum

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
theorem _root_.solution {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (f : weightedTorusScalarL2 k φ)
    (hf : WithLp.toLp 2 (f, (0 : weightedTorusFormL2 k φ)) ∈
      functionDolbeaultGraph k φ) :
    (∀ weakTest, ContDiff ℝ 1 weakTest → HasCompactSupport weakTest →
      ∀ weakCoordinate,
        (∫ weakPoint, (complexTorusCoverLift
        (fun p : WeightedTorusHilbert.LogTorus n => f p)) weakPoint *
          coverBarPartialTest weakTest weakCoordinate weakPoint) = 0) := by
  classical
  intro ψ hψ hψcompact j
  obtain ⟨s, χ, hχ, hχsupport, hpartition⟩ :=
    exists_finite_fundamental_test_partition hψcompact
  let ξ : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n → ℝ :=
    fun i z => χ i z * ψ z
  have hξ : ∀ i, ContDiff ℝ 1 (ξ i) := by
    intro i
    exact (hχ i).mul hψ
  have hξcompact : ∀ i, HasCompactSupport (ξ i) := by
    intro i
    exact hψcompact.mul_left
  have hξcell : ∀ i,
      tsupport (ξ i) ⊆ coverFundamentalCell (coverCenteredFundamentalBase i) := by
    intro i
    apply coverTestWithinFundamentalCell_of_tsupport_subset_interior
    exact tsupport_mul_subset_left.trans (hχsupport i)
  have hψsum : ψ = fun z => ∑ i ∈ s, ξ i z := by
    funext z
    exact hpartition z
  have hloc :=
    weightedScalarL2_complexTorusCoverLift_locallyIntegrable hφ f
  have hint : ∀ i ∈ s, Integrable
      (fun z : TorusCharacters.LogSpace n =>
        complexTorusCoverLift
          (fun p : WeightedTorusHilbert.LogTorus n => f p) z *
            coverBarPartialTest (ξ i) j z)
      (volume : Measure (TorusCharacters.LogSpace n)) := by
    intro i _
    simpa [smul_eq_mul] using
      hloc.integrable_smul_right_of_hasCompactSupport
        (continuous_coverBarPartialTest (hξ i) j)
        (compactSupport_coverBarPartialTest (hξcompact i) j)
  change
    (∫ z : TorusCharacters.LogSpace n,
      complexTorusCoverLift
        (fun p : WeightedTorusHilbert.LogTorus n => f p) z *
          coverBarPartialTest ψ j z
      ∂(volume : Measure (TorusCharacters.LogSpace n))) = 0
  calc
    _ = ∫ z : TorusCharacters.LogSpace n,
        ∑ i ∈ s,
          complexTorusCoverLift
            (fun p : WeightedTorusHilbert.LogTorus n => f p) z *
              coverBarPartialTest (ξ i) j z
        ∂(volume : Measure (TorusCharacters.LogSpace n)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hψsum, coverBarPartialTest_finset_sum s ξ
        (fun i _ => hξ i) j z, Finset.mul_sum]
    _ = ∑ i ∈ s,
        (∫ z : TorusCharacters.LogSpace n,
          complexTorusCoverLift
            (fun p : WeightedTorusHilbert.LogTorus n => f p) z *
              coverBarPartialTest (ξ i) j z
          ∂(volume : Measure
            (TorusCharacters.LogSpace n))) :=
      integral_finsetSum s hint
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact weightedZeroGraph_compact_barPartial_zero_of_fundamentalCell
        hφ f hf (coverCenteredFundamentalBase i)
        (hξ i) (hξcompact i) (hξcell i) j
end Ehrhart.WeightedTorusClosedGraphWeakBridge
