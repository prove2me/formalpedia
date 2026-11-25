-- Prove2me | solution 1 for F6RotationSupport.interval_commonInc_incomparable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:08:58.332968+00:00
-- url     : https://prove2.me/submissions/ee5c7887-f1c4-435e-a004-945334e43681

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
import Theorems.Thm_F6RotationSupport_mem_interval
import Theorems.Thm_F6RotationSupport_mem_commonInc
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
attribute [local simp] F6ConvexWindow.ChainDecomposition.mem_part
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_antichains
attribute [local simp] F6ConvexWindow.mem_ideal


attribute [local simp] F6RotationSupport.mem_interval
attribute [local simp] F6RotationSupport.mem_commonInc

set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]
namespace F6RotationSupport
theorem _root_.solution {alpha beta a z : R}
    (ha : a ∈ interval alpha beta) (hz : z ∈ commonInc alpha beta) :
    F6ConvexWindow.IncRel a z := by
  obtain ⟨hal, hau⟩ := mem_interval.mp ha
  obtain ⟨hza, hzb⟩ := mem_commonInc.mp hz
  exact ⟨fun haz => hza.1 (hal.trans haz), fun hza' => hzb.2 (hza'.trans hau)⟩
end F6RotationSupport
