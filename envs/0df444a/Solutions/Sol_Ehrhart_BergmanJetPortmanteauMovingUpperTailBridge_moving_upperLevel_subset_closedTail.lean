-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.moving_upperLevel_subset_closedTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/bac656bd-4f48-4e94-9bb9-f5a45c5668f5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge
open Set Function Filter MeasureTheory
open BergmanJetPortmanteauSlopeBridge BergmanJetPortmanteauUpperTailBridge
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge
theorem _root_.solution
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → X → ℝ) (t : ℝ)
    {N k : ℕ} (hk : N ≤ k) :
    {x : X | t ≤ f k x} ⊆ movingUpperLevelClosedTail f t N := by
  intro x hx
  apply subset_closure
  exact Set.mem_iUnion.mpr
    ⟨k, Set.mem_iUnion.mpr ⟨hk, hx⟩⟩
end Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge
