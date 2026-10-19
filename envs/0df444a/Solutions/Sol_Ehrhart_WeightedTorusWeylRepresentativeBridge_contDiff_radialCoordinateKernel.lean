-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRepresentativeBridge.contDiff_radialCoordinateKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/ca947485-4c0e-4d6b-9c4a-8048c2f6eba3

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusWeylRepresentativeBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ContDiff Convolution ENNReal Topology
open DolbeaultRegularity DolbeaultGraphDistributionBridge
namespace Ehrhart.WeightedTorusWeylRepresentativeBridge
theorem _root_.solution :
    ContDiff ℝ ∞ radialCoordinateKernel := by
  unfold radialCoordinateKernel
  apply Real.smoothTransition.contDiff.comp
  simp_rw [Complex.normSq_apply]
  have hre : ContDiff ℝ ∞ (fun w : ℂ => w.re) :=
    Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun w : ℂ => w.im) :=
    Complex.imCLM.contDiff
  exact contDiff_const.sub ((hre.mul hre).add (him.mul him))
end Ehrhart.WeightedTorusWeylRepresentativeBridge
