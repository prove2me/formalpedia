-- Prove2me | solution 1 for F6RotationSupport.commonInc_orderConvex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:44:55.157958+00:00
-- url     : https://prove2.me/submissions/8aaddd5d-cf76-4ee1-815f-560d89a33a3c

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
import Theorems.Thm_F6RotationSupport_mem_commonInc
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_incomparability_interval
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
attribute [local simp] F6ConvexWindow.ChainDecomposition.mem_part
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_antichains
attribute [local simp] F6ConvexWindow.mem_ideal


attribute [local simp] F6RotationSupport.mem_commonInc

set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]
namespace F6RotationSupport
theorem _root_.solution (alpha beta : R) : OrderConvex (commonInc alpha beta) := by
  intro x hx z hz y hxy hyz
  obtain ⟨hax, hbx⟩ := mem_commonInc.mp hx
  obtain ⟨haz, hbz⟩ := mem_commonInc.mp hz
  exact mem_commonInc.mpr
    ⟨F6ConvexWindow.incomparability_interval hxy hyz hax haz,
      F6ConvexWindow.incomparability_interval hxy hyz hbx hbz⟩
end F6RotationSupport
