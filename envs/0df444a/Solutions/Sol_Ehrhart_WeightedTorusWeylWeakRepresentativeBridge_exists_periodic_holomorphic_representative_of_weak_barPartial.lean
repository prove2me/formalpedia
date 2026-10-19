-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.exists_periodic_holomorphic_representative_of_weak_barPartial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/38bd377e-06fa-4608-8640-60df2894ffb2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_differentiable_productRadialHolomorphicMollification
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_productRadialHolomorphicMollification_periodic
import Theorems.Thm_Ehrhart_WeightedTorusWeylWeakRepresentativeBridge_productRadialHolomorphicMollification_ae_eq_of_weak

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusWeylWeakRepresentativeBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ContDiff Convolution ENNReal InnerProductSpace Topology
open WeightedBrascampSaturation DolbeaultRegularity ComplexKillingSaturationBridge
open DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusClosedGraphWeakBridge WeightedTorusWeylRepresentativeBridge
open WeightedTorusWeylRadialIntegrationBridge
namespace Ehrhart.WeightedTorusWeylWeakRepresentativeBridge
theorem _root_.solution
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hweak : (∀ weakTest, ContDiff ℝ 1 weakTest → HasCompactSupport weakTest →
      ∀ weakCoordinate,
        (∫ weakPoint, g weakPoint *
          coverBarPartialTest weakTest weakCoordinate weakPoint) = 0))
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic g (TorusCharacters.imaginaryShift q)) :
    ∃ F : TorusCharacters.LogSpace n → ℂ,
      Differentiable ℂ F ∧
        (∀ q : Fin n → ℤ,
          Function.Periodic F
            (TorusCharacters.imaginaryShift q)) ∧
        F =ᵐ[(volume : Measure
          (TorusCharacters.LogSpace n))] g := by
  refine ⟨productRadialHolomorphicMollification g,
    differentiable_productRadialHolomorphicMollification hg hweak,
    ?_, productRadialHolomorphicMollification_ae_eq_of_weak hg hweak⟩
  intro q
  exact productRadialHolomorphicMollification_periodic (hperiod q)
end Ehrhart.WeightedTorusWeylWeakRepresentativeBridge
