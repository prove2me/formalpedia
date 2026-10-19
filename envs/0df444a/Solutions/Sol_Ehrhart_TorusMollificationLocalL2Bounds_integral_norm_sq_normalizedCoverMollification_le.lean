-- Prove2me | solution 1 for Ehrhart.TorusMollificationLocalL2Bounds.integral_norm_sq_normalizedCoverMollification_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/0fe69ef7-f704-413a-a2a1-1dcf583195be

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusMollificationLocalL2Bounds
open Set Function Filter MeasureTheory
open TorusCharacters DolbeaultRegularity TorusWeakDolbeaultMollification
open TorusFriedrichsMollifierEstimates
open scoped BigOperators ENNReal Topology ContDiff Convolution
namespace Ehrhart.TorusMollificationLocalL2Bounds
theorem _root_.solution
    {n : ℕ} {h : LogSpace n → ℂ}
    (hh : MemLp h 2 (volume : Measure (LogSpace n)))
    (k : ℕ) :
    (∫ x : LogSpace n,
      ‖normalizedCoverMollification h k x‖ ^ 2
      ∂(volume : Measure (LogSpace n))) ≤
      ∫ x : LogSpace n, ‖h x‖ ^ 2
        ∂(volume : Measure (LogSpace n)) := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
    ContinuousLinearMap.mul ℝ ℝ
  let q : LogSpace n → ℝ :=
    κ ⋆[L, (volume : Measure (LogSpace n))]
      (fun x : LogSpace n => ‖h x‖ ^ 2)
  have hκ : Continuous κ :=
    (complexShrinkingBump (n := n) k).continuous_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have hκint : Integrable κ (volume : Measure (LogSpace n)) :=
    hκ.integrable_of_hasCompactSupport hκcompact
  have hq : Integrable q (volume : Measure (LogSpace n)) :=
    hκint.integrable_convolution L hh.norm.integrable_sq
  have hsquare : Integrable
      (fun x : LogSpace n =>
        ‖normalizedCoverMollification h k x‖ ^ 2)
      (volume : Measure (LogSpace n)) :=
    (normalizedCoverMollification_memLp hh k).norm.integrable_sq
  calc
    (∫ x : LogSpace n,
      ‖normalizedCoverMollification h k x‖ ^ 2
      ∂(volume : Measure (LogSpace n))) ≤
        ∫ x : LogSpace n, q x
          ∂(volume : Measure (LogSpace n)) := by
          apply integral_mono hsquare hq
          intro x
          simpa [q, κ, L, MeasureTheory.convolution_def] using
            normalizedCoverMollification_norm_sq_le_convolution_norm_sq
              hh k x
    _ =
        (∫ x : LogSpace n, κ x
          ∂(volume : Measure (LogSpace n))) *
        (∫ x : LogSpace n, ‖h x‖ ^ 2
          ∂(volume : Measure (LogSpace n))) := by
          exact MeasureTheory.integral_convolution L
            hκint hh.norm.integrable_sq
    _ = _ := by
      rw [(complexShrinkingBump (n := n) k).integral_normed]
      simp
end Ehrhart.TorusMollificationLocalL2Bounds
