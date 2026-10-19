-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.productRadialWeighted_holomorphic_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/004598ba-59bf-4321-981a-8ba9d89e7b5c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_productRadialWeighted_integral_finset_reset

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
    (hF : Differentiable ℂ F) :
    (∫ w : TorusCharacters.LogSpace n,
      productRadialWeightedIntegrand F w) =
      productRadialKernelMass n • F 0 := by
  have hreset :=
    productRadialWeighted_integral_finset_reset hF
      (Finset.univ : Finset (Fin n))
  have hone :
      holomorphicFinsetReset F (Finset.univ : Finset (Fin n)) =
        (fun _ : TorusCharacters.LogSpace n => F 0) := by
    funext w
    unfold holomorphicFinsetReset
    congr 1
    funext i
    simp
  calc
    (∫ w : TorusCharacters.LogSpace n,
      productRadialWeightedIntegrand F w) =
      ∫ w : TorusCharacters.LogSpace n,
        productRadialWeightedIntegrand
          (fun _ : TorusCharacters.LogSpace n => F 0) w := by
      rw [← hone]
      exact hreset
    _ = (∫ w : TorusCharacters.LogSpace n,
          (productRadialKernel w : ℂ)) * F 0 :=
      MeasureTheory.integral_mul_const _ _
    _ = (productRadialKernelMass n : ℂ) * F 0 := by
      apply congrArg (fun a : ℂ => a * F 0)
      exact integral_complex_ofReal
        (f := productRadialKernel (n := n))
    _ = productRadialKernelMass n • F 0 := by
      rw [Complex.real_smul]
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
