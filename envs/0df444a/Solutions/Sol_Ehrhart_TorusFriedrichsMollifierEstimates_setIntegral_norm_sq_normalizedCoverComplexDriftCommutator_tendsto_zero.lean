-- Prove2me | solution 1 for Ehrhart.TorusFriedrichsMollifierEstimates.setIntegral_norm_sq_normalizedCoverComplexDriftCommutator_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/d89f8e67-55c6-439e-8bc5-d3b427ee0b26

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultRegularity_complexShrinkingBump_rOut_tendsto
import Theorems.Thm_Ehrhart_TorusFriedrichsMollifierEstimates_setIntegral_norm_sq_normalizedCoverComplexDriftCommutator_le

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusFriedrichsMollifierEstimates
open Set Function Filter MeasureTheory
open TorusCharacters DolbeaultRegularity TorusWeakDolbeaultMollification
open scoped BigOperators ENNReal Topology ContDiff Convolution
namespace Ehrhart.TorusFriedrichsMollifierEstimates
theorem _root_.solution
    {n : ℕ} {b h : LogSpace n → ℂ}
    (hh : LocallyIntegrable h (volume : Measure (LogSpace n)))
    (hlocal : ∀ {S : Set (LogSpace n)}, IsCompact S →
      MemLp h 2 ((volume : Measure (LogSpace n)).restrict S))
    (hb : Continuous b)
    {K : Set (LogSpace n)} (hK : IsCompact K) :
    Tendsto
      (fun k : ℕ =>
        ∫ x in K,
          ‖normalizedCoverComplexDriftCommutator b h k x‖ ^ 2
            ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  let S : Set (LogSpace n) := Metric.cthickening 1 K
  have hS : IsCompact S := hK.cthickening
  let M : ℝ :=
    ∫ y in S, ‖h y‖ ^ 2
      ∂(volume : Measure (LogSpace n))
  have hM : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg (fun y => sq_nonneg _)
  have hUC : UniformContinuousOn b S :=
    hS.uniformContinuousOn_of_continuous hb.continuousOn
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hden : 0 < 2 * (M + 1) := by positivity
  let η : ℝ := min 1 (ε / (2 * (M + 1)))
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min zero_lt_one (div_pos hε hden)
  have hηone : η ≤ 1 := min_le_left _ _
  have hηdiv : η ≤ ε / (2 * (M + 1)) := min_le_right _ _
  have hηscale : η * (2 * (M + 1)) ≤ ε :=
    (le_div_iff₀ hden).mp hηdiv
  obtain ⟨δ, hδ, hu⟩ :=
    (Metric.uniformContinuousOn_iff.mp hUC) η hη
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.mp
      (complexShrinkingBump_rOut_tendsto (n := n)))
      (min 1 δ) (lt_min zero_lt_one hδ)
  refine ⟨N, fun k hk => ?_⟩
  have hr : (complexShrinkingBump (n := n) k).rOut < min 1 δ := by
    have hrmetric := hN k hk
    simpa [Real.dist_eq,
      abs_of_nonneg (complexShrinkingBump (n := n) k).rOut_pos.le]
      using hrmetric
  have hrone : (complexShrinkingBump (n := n) k).rOut < 1 :=
    lt_of_lt_of_le hr (min_le_left _ _)
  have hrdelta : (complexShrinkingBump (n := n) k).rOut < δ :=
    lt_of_lt_of_le hr (min_le_right _ _)
  have hkernelDist (x y : LogSpace n)
      (hy : (complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) (x - y) ≠ 0) :
      dist y x < (complexShrinkingBump (n := n) k).rOut := by
    have hball :
        x - y ∈ Metric.ball (0 : LogSpace n)
          (complexShrinkingBump (n := n) k).rOut := by
      rw [← (complexShrinkingBump (n := n) k).support_normed_eq
        (μ := (volume : Measure (LogSpace n)))]
      exact hy
    have hnorm :
        ‖x - y‖ < (complexShrinkingBump (n := n) k).rOut := by
      simpa [Metric.mem_ball, dist_zero_right] using hball
    simpa [dist_eq_norm, norm_sub_rev] using hnorm
  have hreach : ∀ x ∈ K, ∀ y : LogSpace n,
      (complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) (x - y) ≠ 0 → y ∈ S := by
    intro x hx y hy
    change y ∈ Metric.cthickening 1 K
    exact Metric.mem_cthickening_of_dist_le y x 1 K hx
      ((hkernelDist x y hy).le.trans hrone.le)
  have hosc : ∀ x ∈ K, ∀ y : LogSpace n,
      (complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) (x - y) ≠ 0 →
          ‖b y - b x‖ ≤ η := by
    intro x hx y hy
    have hxS : x ∈ S :=
      Metric.self_subset_cthickening K hx
    have hp := hu y (hreach x hx y hy) x hxS
      ((hkernelDist x y hy).trans hrdelta)
    exact le_of_lt (by simpa [dist_eq_norm] using hp)
  have hL2 :=
    setIntegral_norm_sq_normalizedCoverComplexDriftCommutator_le
      hh hb k hK hS (hlocal hS) (c := η) hreach hosc
  have hηsq : η ^ 2 ≤ η := by
    nlinarith [hη.le, hηone]
  have hfirst : η ^ 2 * M ≤ η * M :=
    mul_le_mul_of_nonneg_right hηsq hM
  have hsecond : η * M ≤ η * (M + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hη.le
  have hhalf : η * (M + 1) ≤ ε / 2 := by
    nlinarith [hηscale]
  have hbound : η ^ 2 * M < ε :=
    lt_of_le_of_lt (hfirst.trans (hsecond.trans hhalf)) (by linarith)
  have hnonneg :
      0 ≤ ∫ x in K,
        ‖normalizedCoverComplexDriftCommutator b h k x‖ ^ 2
          ∂(volume : Measure (LogSpace n)) :=
    integral_nonneg (fun x => sq_nonneg _)
  have hfinal :
      (∫ x in K,
        ‖normalizedCoverComplexDriftCommutator b h k x‖ ^ 2
          ∂(volume : Measure (LogSpace n))) < ε := by
    apply lt_of_le_of_lt hL2
    exact hbound
  simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hfinal
end Ehrhart.TorusFriedrichsMollifierEstimates
