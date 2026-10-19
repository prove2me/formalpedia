-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.holomorphicCoordinateReset_finsetReset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/5618e4af-83f7-4894-a7ff-cecc96929696

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    (F : TorusCharacters.LogSpace n → ℂ)
    (s : Finset (Fin n)) (i : Fin n) :
    holomorphicCoordinateReset (holomorphicFinsetReset F s) i =
      holomorphicFinsetReset F (insert i s) := by
  funext w
  unfold holomorphicCoordinateReset holomorphicFinsetReset
  apply congrArg F
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
