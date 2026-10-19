-- Prove2me | solution 1 for Ehrhart.TorusFriedrichsMollifierEstimates.norm_normalizedCoverComplexDriftCommutator_le_driftOscillation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/7dade23f-dbea-451f-b4e8-ef47975d82f9

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusFriedrichsMollifierEstimates_normalizedCoverComplexDriftCommutator_eq_integral

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
    (hb : Continuous b) (k : ℕ) (x : LogSpace n)
    {c : ℝ}
    (hosc : ∀ y : LogSpace n,
      (complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) (x - y) ≠ 0 →
        ‖b y - b x‖ ≤ c) :
    ‖normalizedCoverComplexDriftCommutator b h k x‖ ≤
      c *
        ∫ y : LogSpace n,
          ‖h y‖ *
            (complexShrinkingBump (n := n) k).normed
              (volume : Measure (LogSpace n)) (x - y)
          ∂(volume : Measure (LogSpace n)) := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
    ContinuousLinearMap.lsmul ℝ ℝ
  have hκ : Continuous κ :=
    (complexShrinkingBump (n := n) k).continuous_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have hhnorm : LocallyIntegrable
      (fun y : LogSpace n => ‖h y‖)
      (volume : Measure (LogSpace n)) := by
    exact locallyIntegrableOn_univ.mp
      ((hh.locallyIntegrableOn Set.univ).norm)
  have hbase : Integrable
      (fun y : LogSpace n => ‖h y‖ * κ (x - y))
      (volume : Measure (LogSpace n)) := by
    have hi := hκcompact.convolutionExists_right L hhnorm hκ x
    simpa [L] using hi.integrable
  have hmajor : Integrable
      (fun y : LogSpace n => c * (‖h y‖ * κ (x - y)))
      (volume : Measure (LogSpace n)) := hbase.const_mul c
  rw [normalizedCoverComplexDriftCommutator_eq_integral hh hb k x,
    ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.norm_integral_le_of_norm_le hmajor
  filter_upwards with y
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg
      ((complexShrinkingBump (n := n) k).nonneg_normed (x - y))]
  by_cases hz : κ (x - y) = 0
  · simp [hz, κ]
  · calc
      (‖b y - b x‖ * ‖h y‖) * κ (x - y) ≤
        (c * ‖h y‖) * κ (x - y) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hosc y hz) (norm_nonneg _))
            ((complexShrinkingBump (n := n) k).nonneg_normed
              (x - y))
      _ = c * (‖h y‖ * κ (x - y)) := by ring
end Ehrhart.TorusFriedrichsMollifierEstimates
