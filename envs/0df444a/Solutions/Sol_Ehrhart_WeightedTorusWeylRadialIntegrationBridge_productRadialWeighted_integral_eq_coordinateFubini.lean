-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.productRadialWeighted_integral_eq_coordinateFubini
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/10a2ddaa-ca16-453a-a631-e9e256a35337

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_integrable_productRadialWeightedIntegrand

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
    (hF : Continuous F)
    (i : Fin (n + 1)) :
    (∫ w : TorusCharacters.LogSpace (n + 1),
      productRadialWeightedIntegrand F w) =
      ∫ y : TorusCharacters.LogSpace n,
        ∫ x : ℂ,
          productRadialWeightedIntegrand F
            (i.insertNth x y) := by
  let e :
      (ℂ × TorusCharacters.LogSpace n) ≃ᵐ
        TorusCharacters.LogSpace (n + 1) :=
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℂ) i).symm
  have he : MeasurePreserving e
      ((volume : Measure ℂ).prod
        (volume : Measure
          (TorusCharacters.LogSpace n)))
      (volume : Measure
        (TorusCharacters.LogSpace (n + 1))) := by
    simpa [e, MeasureTheory.volume_pi] using
      (MeasureTheory.measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => (volume : Measure ℂ)) i).symm
  have hi :
      Integrable
        (fun p : ℂ × TorusCharacters.LogSpace n =>
          productRadialWeightedIntegrand F
            (i.insertNth p.1 p.2))
        ((volume : Measure ℂ).prod
          (volume : Measure
            (TorusCharacters.LogSpace n))) := by
    have h := he.integrable_comp_of_integrable
      (integrable_productRadialWeightedIntegrand hF)
    simpa [e, Function.comp_def,
      MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv] using h
  calc
    (∫ w : TorusCharacters.LogSpace (n + 1),
      productRadialWeightedIntegrand F w) =
      ∫ p : ℂ × TorusCharacters.LogSpace n,
        productRadialWeightedIntegrand F
          (i.insertNth p.1 p.2)
        ∂((volume : Measure ℂ).prod
          (volume : Measure
            (TorusCharacters.LogSpace n))) := by
      simpa [e, Function.comp_def,
        MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv] using
          (he.integral_comp'
            (productRadialWeightedIntegrand F)).symm
    _ = ∫ y : TorusCharacters.LogSpace n,
        ∫ x : ℂ,
          productRadialWeightedIntegrand F
            (i.insertNth x y) :=
      MeasureTheory.integral_prod_symm _ hi
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
