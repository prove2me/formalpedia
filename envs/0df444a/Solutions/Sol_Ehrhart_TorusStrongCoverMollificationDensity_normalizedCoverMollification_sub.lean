-- Prove2me | solution 1 for Ehrhart.TorusStrongCoverMollificationDensity.normalizedCoverMollification_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/22e5df52-c7d2-421b-b0e1-f7e57c214b1d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusStrongCoverMollificationDensity
open Set Function Filter MeasureTheory Matrix
open TorusCharacters DolbeaultRegularity MatrixTorusBochnerCoreApproximation
open TorusWeakDolbeaultMollification TorusMollificationLocalL2Bounds TorusStrongCoverMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusStrongCoverMollificationDensity
theorem _root_.solution
    {n : ℕ} {g h : LogSpace n → ℂ}
    (hg : MemLp g 2 (volume : Measure (LogSpace n)))
    (hh : MemLp h 2 (volume : Measure (LogSpace n)))
    (k : ℕ) (x : LogSpace n) :
    normalizedCoverMollification (fun y => g y - h y) k x =
      normalizedCoverMollification g k x -
        normalizedCoverMollification h k x := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  have hc : Continuous κ :=
    (complexShrinkingBump (n := n) k).continuous_normed
  have hs : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have hgi := (hs.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hc
      (hg.locallyIntegrable (by norm_num))) x
  have hhi := (hs.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hc
      (hh.locallyIntegrable (by norm_num))) x
  change
    (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (LogSpace n))]
      (fun y => g y - h y)) x =
    (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (LogSpace n))] g) x -
    (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (LogSpace n))] h) x
  rw [MeasureTheory.convolution_def,
    MeasureTheory.convolution_def,
    MeasureTheory.convolution_def,
    ← MeasureTheory.integral_sub hgi hhi]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [ContinuousLinearMap.map_sub]
end Ehrhart.TorusStrongCoverMollificationDensity
