-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.normalizedProductRadial_holomorphic_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/5cabcce0-00e6-49ab-bdde-c917807fc469

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_productRadialKernelMass_pos
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_productRadialWeighted_holomorphic_integral

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
    (z : TorusCharacters.LogSpace n) :
    (∫ w : TorusCharacters.LogSpace n,
      normalizedProductRadialKernel w • F (z - w)) = F z := by
  let G : TorusCharacters.LogSpace n → ℂ :=
    fun w => F (z - w)
  have hG : Differentiable ℂ G := by
    dsimp [G]
    apply hF.comp
    fun_prop
  have hmass : (productRadialKernelMass n : ℂ) ≠ 0 := by
    exact_mod_cast (productRadialKernelMass_pos n).ne'
  have hpoint (w : TorusCharacters.LogSpace n) :
      normalizedProductRadialKernel w • F (z - w) =
        (productRadialKernelMass n : ℂ)⁻¹ *
          productRadialWeightedIntegrand G w := by
    simp only [normalizedProductRadialKernel,
      productRadialWeightedIntegrand, Complex.real_smul,
      div_eq_mul_inv]
    push_cast
    dsimp [G]
    ring
  calc
    (∫ w : TorusCharacters.LogSpace n,
      normalizedProductRadialKernel w • F (z - w)) =
      ∫ w : TorusCharacters.LogSpace n,
        (productRadialKernelMass n : ℂ)⁻¹ *
          productRadialWeightedIntegrand G w := by
        apply integral_congr_ae
        filter_upwards [] with w
        exact hpoint w
    _ = (productRadialKernelMass n : ℂ)⁻¹ *
          (∫ w : TorusCharacters.LogSpace n,
            productRadialWeightedIntegrand G w) :=
        MeasureTheory.integral_const_mul _ _
    _ = (productRadialKernelMass n : ℂ)⁻¹ *
          (productRadialKernelMass n • G 0) := by
        rw [productRadialWeighted_holomorphic_integral hG]
    _ = F z := by
        dsimp [G]
        simp [hmass]
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
