-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.antitone_movingUpperLevelClosedTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/f7c47d0a-1e0d-47db-b28a-4ebceacff902

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
    (f : ℕ → X → ℝ) (t : ℝ) :
    Antitone (movingUpperLevelClosedTail f t) := by
  intro m n hmn
  apply closure_mono
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
  rcases Set.mem_iUnion.mp hk with ⟨hnk, hxk⟩
  exact Set.mem_iUnion.mpr
    ⟨k, Set.mem_iUnion.mpr ⟨le_trans hmn hnk, hxk⟩⟩
end Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge
