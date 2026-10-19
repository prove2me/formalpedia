-- Prove2me | solution 1 for Ehrhart.BergmanJetBodyExponentialSecantBridge.nonnegative_le_exp_mul_one_sub_exp_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/5669016c-2835-4924-a575-0f2e16303e78

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetBodyExponentialSecantBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity
open BergmanJetPartitionEndpoint BergmanJetTorusRightSlopeGibbsBridge
open BergmanJetBodyLogPartitionSharpGrowth
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetBodyExponentialSecantBridge
theorem _root_.solution
    {u C : ℝ} (hu : 0 ≤ u) (huC : u ≤ C) :
    u ≤ Real.exp C * (1 - Real.exp (-u)) := by
  have hexp := mul_le_mul_of_nonneg_right
    (Real.add_one_le_exp u) (Real.exp_pos (-u)).le
  have hcancel : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hcancel] at hexp
  have hfactor : u * Real.exp (-u) ≤ 1 - Real.exp (-u) := by
    nlinarith
  calc
    u = u * 1 := by ring
    _ ≤ u * Real.exp (C - u) := by
      apply mul_le_mul_of_nonneg_left _ hu
      exact Real.one_le_exp (sub_nonneg.mpr huC)
    _ = Real.exp C * (u * Real.exp (-u)) := by
      rw [show C - u = C + -u by ring, Real.exp_add]
      ring
    _ ≤ Real.exp C * (1 - Real.exp (-u)) :=
      mul_le_mul_of_nonneg_left hfactor (Real.exp_pos C).le
end Ehrhart.BergmanJetBodyExponentialSecantBridge
