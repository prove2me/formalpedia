-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.productRadialWeighted_slice_integral_reset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/dd89f5ad-4bdb-456b-930d-d663e1138d2b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_radialCoordinateKernel_holomorphic_integral_at_zero
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_productRadialKernel_insertNth
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_differentiable_insertNth_holomorphicSlice
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_update_insertNth_zero

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
    {n : ℕ}
    {F : TorusCharacters.LogSpace (n + 1) → ℂ}
    (hF : Differentiable ℂ F)
    (i : Fin (n + 1))
    (y : TorusCharacters.LogSpace n) :
    (∫ x : ℂ,
      productRadialWeightedIntegrand F (i.insertNth x y)) =
      ∫ x : ℂ,
        productRadialWeightedIntegrand
          (holomorphicCoordinateReset F i)
          (i.insertNth x y) := by
  let g : ℂ → ℂ := fun x => F (i.insertNth x y)
  have hg : Differentiable ℂ g :=
    differentiable_insertNth_holomorphicSlice hF i y
  have hrad :
      (∫ x : ℂ, (radialCoordinateKernel x : ℂ) * g x) =
        (↑(∫ x : ℂ, radialCoordinateKernel x) : ℂ) * g 0 := by
    simpa only [Complex.real_smul] using
      radialCoordinateKernel_holomorphic_integral_at_zero hg
  have hbase :
      (∫ x : ℂ, (radialCoordinateKernel x : ℂ) * g 0) =
        (↑(∫ x : ℂ, radialCoordinateKernel x) : ℂ) * g 0 := by
    calc
      (∫ x : ℂ, (radialCoordinateKernel x : ℂ) * g 0) =
        (∫ x : ℂ, (radialCoordinateKernel x : ℂ)) * g 0 :=
        MeasureTheory.integral_mul_const _ _
      _ = (↑(∫ x : ℂ, radialCoordinateKernel x) : ℂ) * g 0 :=
        congrArg (fun a : ℂ => a * g 0)
          (integral_complex_ofReal (f := radialCoordinateKernel))
  have hpoint (x : ℂ) :
      productRadialWeightedIntegrand F (i.insertNth x y) =
        (productRadialKernel y : ℂ) *
          ((radialCoordinateKernel x : ℂ) * g x) := by
    change
      (productRadialKernel (i.insertNth x y) : ℂ) *
        F (i.insertNth x y) = _
    rw [productRadialKernel_insertNth]
    push_cast
    dsimp [g]
    ring
  have hreset (x : ℂ) :
      productRadialWeightedIntegrand
        (holomorphicCoordinateReset F i) (i.insertNth x y) =
        (productRadialKernel y : ℂ) *
          ((radialCoordinateKernel x : ℂ) * g 0) := by
    change
      (productRadialKernel (i.insertNth x y) : ℂ) *
        F (Function.update
          (i.insertNth x y : Fin (n + 1) → ℂ) i 0) = _
    rw [productRadialKernel_insertNth, update_insertNth_zero]
    push_cast
    dsimp [g]
    ring
  calc
    (∫ x : ℂ,
      productRadialWeightedIntegrand F (i.insertNth x y)) =
      ∫ x : ℂ,
        (productRadialKernel y : ℂ) *
          ((radialCoordinateKernel x : ℂ) * g x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hpoint x
    _ = (productRadialKernel y : ℂ) *
        (∫ x : ℂ, (radialCoordinateKernel x : ℂ) * g x) :=
      MeasureTheory.integral_const_mul _ _
    _ = (productRadialKernel y : ℂ) *
        ((↑(∫ x : ℂ, radialCoordinateKernel x) : ℂ) * g 0) := by
      rw [hrad]
    _ = (productRadialKernel y : ℂ) *
        (∫ x : ℂ, (radialCoordinateKernel x : ℂ) * g 0) := by
      rw [hbase]
    _ = ∫ x : ℂ,
        (productRadialKernel y : ℂ) *
          ((radialCoordinateKernel x : ℂ) * g 0) :=
      (MeasureTheory.integral_const_mul _ _).symm
    _ = ∫ x : ℂ,
      productRadialWeightedIntegrand
        (holomorphicCoordinateReset F i) (i.insertNth x y) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (hreset x).symm
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
