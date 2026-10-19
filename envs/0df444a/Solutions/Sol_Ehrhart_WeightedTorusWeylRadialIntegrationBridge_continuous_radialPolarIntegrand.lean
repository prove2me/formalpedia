-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.continuous_radialPolarIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/ae6e6fa6-71b2-49bc-b3d3-94adf9d82e41

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_contDiff_radialCoordinateKernel
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_continuous_complexPolarSymm

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusWeylRadialIntegrationBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ContDiff Convolution ENNReal Topology
open WeightedTorusWeylRepresentativeBridge
namespace Ehrhart.WeightedTorusWeylRadialIntegrationBridge
theorem _root_.solution
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    Continuous (radialPolarIntegrand f c) := by
  unfold radialPolarIntegrand
  apply Continuous.mul (Complex.continuous_ofReal.comp continuous_fst)
  apply Continuous.mul
    (Complex.continuous_ofReal.comp
      (contDiff_radialCoordinateKernel.continuous.comp
        continuous_complexPolarSymm))
  exact hf.continuous.comp
    (continuous_const.sub continuous_complexPolarSymm)
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
