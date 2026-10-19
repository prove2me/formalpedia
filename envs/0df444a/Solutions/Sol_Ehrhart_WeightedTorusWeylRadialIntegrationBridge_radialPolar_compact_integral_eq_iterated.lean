-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.radialPolar_compact_integral_eq_iterated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/148d208a-6350-4339-afa0-f7a6e5e6f933

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_radialPolarIntegrand_integrableOn_compactDomain
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_compactPolarDomain_volume

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
    (∫ p : ℝ × ℝ in compactPolarDomain,
      radialPolarIntegrand f c p) =
      ∫ r : ℝ in Set.Ioc (0 : ℝ) 1,
        ∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
          radialPolarIntegrand f c (r, θ) := by
  let μr : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)
  let μθ : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi)
  have hmeasure :
      (volume : Measure (ℝ × ℝ)).restrict compactPolarDomain =
        μr.prod μθ := compactPolarDomain_volume
  have hi : Integrable (radialPolarIntegrand f c) (μr.prod μθ) := by
    rw [← hmeasure]
    exact radialPolarIntegrand_integrableOn_compactDomain hf c
  calc
    (∫ p : ℝ × ℝ in compactPolarDomain,
      radialPolarIntegrand f c p) =
      ∫ p : ℝ × ℝ, radialPolarIntegrand f c p ∂(μr.prod μθ) := by
        rw [← hmeasure]
    _ = ∫ r : ℝ, ∫ θ : ℝ,
      radialPolarIntegrand f c (r, θ) ∂μθ ∂μr :=
      MeasureTheory.integral_prod _ hi
    _ = ∫ r : ℝ in Set.Ioc (0 : ℝ) 1,
      ∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
        radialPolarIntegrand f c (r, θ) := rfl
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
