-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.integrable_productRadialWeightedIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/1761d244-124e-4b67-9ac8-68ca973b36df

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_continuous_productRadialWeightedIntegrand
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_hasCompactSupport_productRadialWeightedIntegrand

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
theorem _root_.solution {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Continuous F) :
    Integrable (productRadialWeightedIntegrand F)
      (volume : Measure
        (TorusCharacters.LogSpace n)) :=
  (continuous_productRadialWeightedIntegrand hF).integrable_of_hasCompactSupport
    (hasCompactSupport_productRadialWeightedIntegrand F)
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
