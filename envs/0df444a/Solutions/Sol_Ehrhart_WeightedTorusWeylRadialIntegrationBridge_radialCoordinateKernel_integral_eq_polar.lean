-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.radialCoordinateKernel_integral_eq_polar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/bdadb77f-aec8-49d8-b19d-98093082915c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    (f : ℂ → ℂ) (c : ℂ) :
    (∫ w : ℂ, radialCoordinateKernel w • f (c - w)) =
      ∫ p : ℝ × ℝ in Complex.polarCoord.target,
        radialPolarIntegrand f c p := by
  calc
    (∫ w : ℂ, radialCoordinateKernel w • f (c - w)) =
        ∫ p : ℝ × ℝ in Complex.polarCoord.target,
          p.1 •
            (radialCoordinateKernel (Complex.polarCoord.symm p) •
              f (c - Complex.polarCoord.symm p)) :=
      (Complex.integral_comp_polarCoord_symm
        (fun w : ℂ => radialCoordinateKernel w • f (c - w))).symm
    _ = ∫ p : ℝ × ℝ in Complex.polarCoord.target,
        radialPolarIntegrand f c p := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        simp only [radialPolarIntegrand, Complex.real_smul]
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
