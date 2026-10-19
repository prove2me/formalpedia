-- Prove2me | solution 1 for Ehrhart.TorusFriedrichsMollifierEstimates.setIntegral_norm_sq_normalizedCoverComplexDriftCommutator_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/9fe18178-78df-4c8b-bf3e-4a5217ca40c3

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusFriedrichsMollifierEstimates_norm_normalizedCoverComplexDriftCommutator_le_driftOscillation
import Theorems.Thm_Ehrhart_TorusFriedrichsMollifierEstimates_coverReal_convolution_comm

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
    (hb : Continuous b) (k : ℕ)
    {K S : Set (LogSpace n)}
    (hK : IsCompact K) (hS : IsCompact S)
    (hlocal : MemLp h 2 ((volume : Measure (LogSpace n)).restrict S))
    {c : ℝ}
    (hreach : ∀ x ∈ K, ∀ y : LogSpace n,
      (complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) (x - y) ≠ 0 → y ∈ S)
    (hosc : ∀ x ∈ K, ∀ y : LogSpace n,
      (complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) (x - y) ≠ 0 →
          ‖b y - b x‖ ≤ c) :
    (∫ x in K,
      ‖normalizedCoverComplexDriftCommutator b h k x‖ ^ 2
        ∂(volume : Measure (LogSpace n))) ≤
      c ^ 2 *
        ∫ y in S, ‖h y‖ ^ 2
          ∂(volume : Measure (LogSpace n)) := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
    ContinuousLinearMap.mul ℝ ℝ
  let t : LogSpace n → ℂ := S.indicator h
  let q : LogSpace n → ℝ :=
    κ ⋆[L, (volume : Measure (LogSpace n))]
      (fun y : LogSpace n => ‖t y‖ ^ 2)
  have hκ : Continuous κ :=
    (complexShrinkingBump (n := n) k).continuous_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have hκint : Integrable κ (volume : Measure (LogSpace n)) :=
    hκ.integrable_of_hasCompactSupport hκcompact
  have ht : MemLp t 2 (volume : Measure (LogSpace n)) :=
    (MeasureTheory.memLp_indicator_iff_restrict hS.measurableSet).mpr hlocal
  have hq : Integrable q (volume : Measure (LogSpace n)) :=
    hκint.integrable_convolution L ht.norm.integrable_sq
  have hqnonneg (x : LogSpace n) : 0 ≤ q x := by
    unfold q
    rw [MeasureTheory.convolution_def]
    apply integral_nonneg
    intro y
    change 0 ≤ κ y * ‖t (x - y)‖ ^ 2
    exact mul_nonneg
      ((complexShrinkingBump (n := n) k).nonneg_normed y)
      (sq_nonneg _)
  have htotal :
      (∫ x : LogSpace n, q x
        ∂(volume : Measure (LogSpace n))) =
        ∫ y in S, ‖h y‖ ^ 2
          ∂(volume : Measure (LogSpace n)) := by
    calc
      (∫ x : LogSpace n, q x
        ∂(volume : Measure (LogSpace n))) =
        (∫ y : LogSpace n, κ y
          ∂(volume : Measure (LogSpace n))) *
          (∫ y : LogSpace n, ‖t y‖ ^ 2
            ∂(volume : Measure (LogSpace n))) := by
            exact MeasureTheory.integral_convolution L
              hκint ht.norm.integrable_sq
      _ = ∫ y : LogSpace n, ‖t y‖ ^ 2
            ∂(volume : Measure (LogSpace n)) := by
            rw [(complexShrinkingBump (n := n) k).integral_normed]
            simp
      _ = _ := by
        have hsquare :
            (fun y : LogSpace n => ‖t y‖ ^ 2) =
              S.indicator (fun y : LogSpace n => ‖h y‖ ^ 2) := by
          funext y
          by_cases hy : y ∈ S
          · simp [t, hy]
          · simp [t, hy]
        rw [hsquare, MeasureTheory.integral_indicator hS.measurableSet]
  have havg (x : LogSpace n) (hx : x ∈ K) :
      (∫ y : LogSpace n, ‖h y‖ * κ (x - y)
        ∂(volume : Measure (LogSpace n))) =
        ∫ z : LogSpace n, κ z * ‖t (x - z)‖
          ∂(volume : Measure (LogSpace n)) := by
    calc
      (∫ y : LogSpace n, ‖h y‖ * κ (x - y)
        ∂(volume : Measure (LogSpace n))) =
          ((fun y : LogSpace n => ‖h y‖)
            ⋆[L, (volume : Measure (LogSpace n))] κ) x := by
              rfl
      _ = ((fun y : LogSpace n => ‖t y‖)
            ⋆[L, (volume : Measure (LogSpace n))] κ) x := by
        rw [MeasureTheory.convolution_def,
          MeasureTheory.convolution_def]
        apply integral_congr_ae
        filter_upwards with y
        by_cases hy : κ (x - y) = 0
        · simp [L, hy]
        · have hyS : y ∈ S := hreach x hx y hy
          simp [L, t, hyS]
      _ = (κ ⋆[L, (volume : Measure (LogSpace n))]
            (fun y : LogSpace n => ‖t y‖)) x := by
        exact congrFun (coverReal_convolution_comm
          (fun y : LogSpace n => ‖t y‖) κ) x
      _ = ∫ z : LogSpace n, κ z * ‖t (x - z)‖
          ∂(volume : Measure (LogSpace n)) := by
            rfl
  have hpoint (x : LogSpace n) (hx : x ∈ K) :
      ‖normalizedCoverComplexDriftCommutator b h k x‖ ^ 2 ≤
        c ^ 2 * q x := by
    have hbound :=
      norm_normalizedCoverComplexDriftCommutator_le_driftOscillation
        hh hb k x (hosc x hx)
    change
      ‖normalizedCoverComplexDriftCommutator b h k x‖ ≤
        c *
          (∫ y : LogSpace n, ‖h y‖ * κ (x - y)
            ∂(volume : Measure (LogSpace n))) at hbound
    rw [havg x hx] at hbound
    have hJ := normalizedCoverBump_convolution_sq_le_convolution_sq
      ht.norm k x
    have hJ' :
        (∫ z : LogSpace n, κ z * ‖t (x - z)‖
          ∂(volume : Measure (LogSpace n))) ^ 2 ≤ q x := by
      simpa [κ, q, L, MeasureTheory.convolution_def] using hJ
    calc
      ‖normalizedCoverComplexDriftCommutator b h k x‖ ^ 2 ≤
        (c *
          (∫ z : LogSpace n, κ z * ‖t (x - z)‖
            ∂(volume : Measure (LogSpace n)))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hbound 2
      _ = c ^ 2 *
          (∫ z : LogSpace n, κ z * ‖t (x - z)‖
            ∂(volume : Measure (LogSpace n))) ^ 2 := by
              ring
      _ ≤ c ^ 2 * q x :=
          mul_le_mul_of_nonneg_left hJ' (sq_nonneg c)
  have hcommcontinuous :
      Continuous (normalizedCoverComplexDriftCommutator b h k) :=
    continuous_normalizedCoverComplexDriftCommutator hh hb k
  have hcommint : IntegrableOn
      (fun x : LogSpace n =>
        ‖normalizedCoverComplexDriftCommutator b h k x‖ ^ 2)
      K (volume : Measure (LogSpace n)) :=
    (hcommcontinuous.norm.pow 2).continuousOn.integrableOn_compact hK
  have hmajorint : IntegrableOn
      (fun x : LogSpace n => c ^ 2 * q x)
      K (volume : Measure (LogSpace n)) :=
    (hq.const_mul (c ^ 2)).integrableOn
  calc
    (∫ x in K,
      ‖normalizedCoverComplexDriftCommutator b h k x‖ ^ 2
        ∂(volume : Measure (LogSpace n))) ≤
        ∫ x in K, c ^ 2 * q x
          ∂(volume : Measure (LogSpace n)) :=
      MeasureTheory.setIntegral_mono_on
        hcommint hmajorint hK.measurableSet hpoint
    _ = c ^ 2 *
        (∫ x in K, q x
          ∂(volume : Measure (LogSpace n))) := by
            rw [MeasureTheory.integral_const_mul]
    _ ≤ c ^ 2 *
        (∫ x : LogSpace n, q x
          ∂(volume : Measure (LogSpace n))) :=
        mul_le_mul_of_nonneg_left
          (MeasureTheory.setIntegral_le_integral hq
            (Filter.Eventually.of_forall hqnonneg))
          (sq_nonneg c)
    _ = _ := by rw [htotal]
end Ehrhart.TorusFriedrichsMollifierEstimates
