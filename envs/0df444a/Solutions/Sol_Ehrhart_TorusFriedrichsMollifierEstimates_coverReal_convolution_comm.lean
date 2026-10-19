-- Prove2me | solution 1 for Ehrhart.TorusFriedrichsMollifierEstimates.coverReal_convolution_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/85579e2d-90cf-496f-ad89-a25623d60798

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
theorem _root_.solution {n : ℕ}
    (f g : LogSpace n → ℝ) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ,
      (volume : Measure (LogSpace n))] g) =
      (g ⋆[ContinuousLinearMap.mul ℝ ℝ,
        (volume : Measure (LogSpace n))] f) := by
  have h := MeasureTheory.convolution_flip
    (μ := (volume : Measure (LogSpace n)))
    (f := g) (g := f) (ContinuousLinearMap.mul ℝ ℝ)
  rw [ContinuousLinearMap.flip_mul] at h
  exact h
end Ehrhart.TorusFriedrichsMollifierEstimates
