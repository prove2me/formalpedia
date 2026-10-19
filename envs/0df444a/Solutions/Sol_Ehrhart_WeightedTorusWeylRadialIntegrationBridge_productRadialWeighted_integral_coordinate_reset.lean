-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.productRadialWeighted_integral_coordinate_reset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/72021bc4-14bf-4ed6-8ae1-324947597df4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_productRadialWeighted_integral_eq_coordinateFubini
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_differentiable_holomorphicCoordinateReset
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_productRadialWeighted_slice_integral_reset

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
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (i : Fin n) :
    (∫ w : TorusCharacters.LogSpace n,
      productRadialWeightedIntegrand F w) =
      ∫ w : TorusCharacters.LogSpace n,
        productRadialWeightedIntegrand
          (holomorphicCoordinateReset F i) w := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    calc
      (∫ w : TorusCharacters.LogSpace (n + 1),
        productRadialWeightedIntegrand F w) =
        ∫ y : TorusCharacters.LogSpace n,
          ∫ x : ℂ,
            productRadialWeightedIntegrand F
              (i.insertNth x y) :=
        productRadialWeighted_integral_eq_coordinateFubini
          hF.continuous i
      _ = ∫ y : TorusCharacters.LogSpace n,
          ∫ x : ℂ,
            productRadialWeightedIntegrand
              (holomorphicCoordinateReset F i)
              (i.insertNth x y) := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact productRadialWeighted_slice_integral_reset hF i y
      _ = ∫ w : TorusCharacters.LogSpace (n + 1),
          productRadialWeightedIntegrand
            (holomorphicCoordinateReset F i) w :=
        (productRadialWeighted_integral_eq_coordinateFubini
          (differentiable_holomorphicCoordinateReset hF i).continuous
          i).symm
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
