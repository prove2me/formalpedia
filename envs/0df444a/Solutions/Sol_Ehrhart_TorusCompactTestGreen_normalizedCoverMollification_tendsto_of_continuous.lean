-- Prove2me | solution 1 for Ehrhart.TorusCompactTestGreen.normalizedCoverMollification_tendsto_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/6d14c903-c72a-407a-9b0d-e0532857b4eb

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultRegularity_complexShrinkingBump_rOut_tendsto

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
    (hg : Continuous g) (x : LogSpace n) :
    Tendsto (fun k : ℕ => normalizedCoverMollification g k x)
      atTop (nhds (g x)) := by
  exact ContDiffBump.convolution_tendsto_right_of_continuous
    (complexShrinkingBump_rOut_tendsto (n := n)) hg x
end Ehrhart.TorusCompactTestGreen
