-- Prove2me | solution 1 for Ehrhart.TorusCompactTestGreen.norm_normalizedCoverMollification_le_of_continuous_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/8f6add8e-64f5-48f1-a653-dbb9289c4783

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusCompactTestGreen
open Set Function Filter MeasureTheory Matrix
open TorusCharacters DolbeaultRegularity TorusWeakDolbeaultMollification
open TorusMollificationLocalL2Bounds
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusCompactTestGreen
theorem _root_.solution
    {n : ℕ} {g : LogSpace n → ℂ}
    (hg : Continuous g) {B : ℝ}
    (hB : 0 ≤ B) (hgb : ∀ x : LogSpace n, ‖g x‖ ≤ B)
    (k : ℕ) (x : LogSpace n) :
    ‖normalizedCoverMollification g k x‖ ≤ B := by
  have ht := MeasureTheory.dist_convolution_le
    (μ := (volume : Measure (LogSpace n)))
    (f := (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n)))
    (g := g) (x₀ := x)
    (R := (complexShrinkingBump (n := n) k).rOut)
    (ε := B) (z₀ := (0 : ℂ)) hB
    (by
      rw [(complexShrinkingBump (n := n) k).support_normed_eq])
    ((complexShrinkingBump (n := n) k).nonneg_normed)
    ((complexShrinkingBump (n := n) k).integral_normed)
    hg.aestronglyMeasurable
    (by
      intro y _
      simpa [dist_zero_right] using hgb y)
  simpa [normalizedCoverMollification, dist_zero_right] using ht
end Ehrhart.TorusCompactTestGreen
