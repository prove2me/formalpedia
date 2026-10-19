-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.radialPolarIntegral_eq_compactDomain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/24773dab-fb21-460c-a55c-ab150177b69e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_compactPolarDomain_subset_polarTarget
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_radialPolarIntegrand_eq_zero_outside_compactDomain

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
    (∫ p : ℝ × ℝ in Complex.polarCoord.target,
      radialPolarIntegrand f c p) =
      ∫ p : ℝ × ℝ in compactPolarDomain,
        radialPolarIntegrand f c p := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    Complex.polarCoord.open_target.measurableSet
    compactPolarDomain_subset_polarTarget
  intro p hp
  exact radialPolarIntegrand_eq_zero_outside_compactDomain
    f c p hp.1 hp.2
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
