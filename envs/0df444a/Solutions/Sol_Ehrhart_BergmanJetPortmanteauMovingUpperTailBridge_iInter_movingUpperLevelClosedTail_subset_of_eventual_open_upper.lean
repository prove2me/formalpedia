-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge.iInter_movingUpperLevelClosedTail_subset_of_eventual_open_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/1abd2126-009e-47a2-b0c4-7cee806586fb

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
    (f : ℕ → X → ℝ) (g : X → ℝ)
    (hjoint : ∀ (x : X) (t : ℝ), g x < t →
      ∃ (N : ℕ) (U : Set X), IsOpen U ∧ x ∈ U ∧
        ∀ (k : ℕ), N ≤ k → ∀ y ∈ U, f k y < t)
    (t : ℝ) :
    (⋂ N : ℕ, movingUpperLevelClosedTail f t N) ⊆
      {x : X | t ≤ g x} := by
  intro x hx
  change t ≤ g x
  by_contra hnot
  have hlt : g x < t := lt_of_not_ge hnot
  obtain ⟨N, U, hU, hxU, hupper⟩ := hjoint x t hlt
  have hxclose : x ∈ movingUpperLevelClosedTail f t N :=
    Set.mem_iInter.mp hx N
  change x ∈ closure
    (⋃ k : ℕ, ⋃ (_ : N ≤ k), {y : X | t ≤ f k y}) at hxclose
  obtain ⟨y, hyU, hytail⟩ :=
    (mem_closure_iff.mp hxclose) U hU hxU
  obtain ⟨k, hyk⟩ := Set.mem_iUnion.mp hytail
  obtain ⟨hk, hylevel⟩ := Set.mem_iUnion.mp hyk
  exact (not_le_of_gt (hupper k hk y hyU)) hylevel
end Ehrhart.BergmanJetPortmanteauMovingUpperTailBridge
