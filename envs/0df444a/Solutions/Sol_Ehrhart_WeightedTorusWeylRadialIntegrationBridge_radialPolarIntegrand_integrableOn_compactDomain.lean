-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.radialPolarIntegrand_integrableOn_compactDomain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/e7040392-e8ec-421f-b3ea-ee0c4cd25f15

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_continuous_radialPolarIntegrand

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
    IntegrableOn (radialPolarIntegrand f c)
      compactPolarDomain (volume : Measure (ℝ × ℝ)) := by
  have hcompact :
      IsCompact
        (Set.Icc (0 : ℝ) 1 ×ˢ
          Set.Icc (-Real.pi) Real.pi) :=
    isCompact_Icc.prod isCompact_Icc
  have hi : IntegrableOn (radialPolarIntegrand f c)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-Real.pi) Real.pi)
      (volume : Measure (ℝ × ℝ)) :=
    (continuous_radialPolarIntegrand hf c).continuousOn.integrableOn_compact
      hcompact
  apply hi.mono_set
  intro p hp
  exact ⟨⟨hp.1.1.le, hp.1.2⟩,
    ⟨hp.2.1.le, hp.2.2.le⟩⟩
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
