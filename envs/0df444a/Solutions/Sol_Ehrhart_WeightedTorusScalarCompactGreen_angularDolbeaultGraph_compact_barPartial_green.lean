-- Prove2me | solution 1 for Ehrhart.WeightedTorusScalarCompactGreen.angularDolbeaultGraph_compact_barPartial_green
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/4daae793-1db0-43f5-9ac5-5e2e2ebfa645

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_coverTestWithinFundamentalCell_of_tsupport_subset_interior
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_exists_finite_fundamental_test_partition
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_coverBarPartialTest_finset_sum
import Theorems.Thm_Ehrhart_WeightedTorusScalarCompactGreen_angularDolbeaultGraph_compact_barPartial_green_of_fundamentalCell

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusScalarCompactGreen
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault
open TorusWeakDolbeaultMollification TorusMollifiedBochner BergmanJetStrictMixedLocalCore
open MatrixTorusCompactGreen
open scoped BigOperators ENNReal InnerProductSpace Topology
  ComplexConjugate ContDiff Convolution Manifold
namespace Ehrhart.WeightedTorusScalarCompactGreen
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (f : angularWeightedScalarL2 a)
    (W : angularWeightedFormL2 a)
    (hgraph : WithLp.toLp 2 (f, W) ∈ angularDolbeaultGraph a)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    (∫ z : LogSpace n,
      complexTorusCoverLift (fun q : LogTorus n => f q) z *
        coverBarPartialTest ψ j z
      ∂(volume : Measure (LogSpace n))) =
      -(2 : ℂ) *
        (∫ z : LogSpace n,
          complexTorusCoverLift
            (fun q : LogTorus n =>
              (W q : EuclideanSpace ℂ (Fin n)) j) z * (ψ z : ℂ)
          ∂(volume : Measure (LogSpace n))) := by
  classical
  obtain ⟨s, χ, hχ, hχsupport, hpartition⟩ :=
    exists_finite_fundamental_test_partition hψcompact
  let ξ : LogSpace n → LogSpace n → ℝ :=
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
  have hfloc := angularWeightedScalarCoverLift_locallyIntegrable
    ha f
  have hwloc := angularWeightedFormCoordinateCoverLift_locallyIntegrable
    ha W j
  have hintf : ∀ i ∈ s, Integrable
      (fun z : LogSpace n =>
        complexTorusCoverLift
          (fun q : LogTorus n => f q) z *
            coverBarPartialTest (ξ i) j z)
      (volume : Measure (LogSpace n)) := by
    intro i _
    simpa [smul_eq_mul] using
      hfloc.integrable_smul_right_of_hasCompactSupport
        (continuous_coverBarPartialTest (hξ i) j)
        (compactSupport_coverBarPartialTest (hξcompact i) j)
  have hintw : ∀ i ∈ s, Integrable
      (fun z : LogSpace n =>
        complexTorusCoverLift
          (fun q : LogTorus n =>
            (W q : EuclideanSpace ℂ (Fin n)) j) z *
              (ξ i z : ℂ))
      (volume : Measure (LogSpace n)) := by
    intro i _
    simpa [smul_eq_mul] using
      hwloc.integrable_smul_right_of_hasCompactSupport
        (Complex.continuous_ofReal.comp (hξ i).continuous)
        (compactSupport_complexOfReal (hξcompact i))
  calc
    _ = ∫ z : LogSpace n,
        ∑ i ∈ s,
          complexTorusCoverLift
            (fun q : LogTorus n => f q) z *
              coverBarPartialTest (ξ i) j z
        ∂(volume : Measure (LogSpace n)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hψsum, coverBarPartialTest_finset_sum s ξ
        (fun i _ => hξ i) j z, Finset.mul_sum]
    _ = ∑ i ∈ s,
      (∫ z : LogSpace n,
        complexTorusCoverLift
          (fun q : LogTorus n => f q) z *
            coverBarPartialTest (ξ i) j z
        ∂(volume : Measure (LogSpace n))) :=
      integral_finsetSum s hintf
    _ = ∑ i ∈ s,
      (-(2 : ℂ) *
        (∫ z : LogSpace n,
          complexTorusCoverLift
            (fun q : LogTorus n =>
              (W q : EuclideanSpace ℂ (Fin n)) j) z *
                (ξ i z : ℂ)
          ∂(volume : Measure (LogSpace n)))) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact angularDolbeaultGraph_compact_barPartial_green_of_fundamentalCell
        ha f W hgraph (coverCenteredFundamentalBase i)
        (hξ i) (hξcompact i) (hξcell i) j
    _ = -(2 : ℂ) *
      (∫ z : LogSpace n,
        ∑ i ∈ s,
          complexTorusCoverLift
            (fun q : LogTorus n =>
              (W q : EuclideanSpace ℂ (Fin n)) j) z *
                (ξ i z : ℂ)
        ∂(volume : Measure (LogSpace n))) := by
      rw [integral_finsetSum s hintw]
      simp [Finset.mul_sum]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hpartition z]
      simp [ξ, Finset.mul_sum]
end Ehrhart.WeightedTorusScalarCompactGreen
