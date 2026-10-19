-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.productRadialWeighted_integral_finset_reset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/bfb1fd2a-8f95-407f-96e9-615727034f8f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_productRadialWeighted_integral_coordinate_reset
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_differentiable_holomorphicFinsetReset
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_holomorphicCoordinateReset_finsetReset

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
    (s : Finset (Fin n)) :
    (∫ w : TorusCharacters.LogSpace n,
      productRadialWeightedIntegrand F w) =
      ∫ w : TorusCharacters.LogSpace n,
        productRadialWeightedIntegrand
          (holomorphicFinsetReset F s) w := by
  induction s using Finset.induction_on with
  | empty =>
    rfl
  | @insert i s hi ih =>
    calc
      (∫ w : TorusCharacters.LogSpace n,
        productRadialWeightedIntegrand F w) =
        ∫ w : TorusCharacters.LogSpace n,
          productRadialWeightedIntegrand
            (holomorphicFinsetReset F s) w := ih
      _ = ∫ w : TorusCharacters.LogSpace n,
          productRadialWeightedIntegrand
            (holomorphicCoordinateReset
              (holomorphicFinsetReset F s) i) w :=
        productRadialWeighted_integral_coordinate_reset
          (differentiable_holomorphicFinsetReset hF s) i
      _ = ∫ w : TorusCharacters.LogSpace n,
          productRadialWeightedIntegrand
            (holomorphicFinsetReset F (insert i s)) w := by
        rw [holomorphicCoordinateReset_finsetReset]
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
