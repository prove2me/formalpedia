-- Prove2me | solution 1 for F6RotationSupport.two_le_card_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:18:25.441795+00:00
-- url     : https://prove2.me/submissions/14e9c812-ecde-4f48-8851-ac1589e8fd95

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
import Theorems.Thm_F6RotationSupport_mem_supportUnion
import Theorems.Thm_F6RotationSupport_mem_interval
import Theorems.Thm_F6RotationSupport_mem_commonInc
import Theorems.Thm_F6RotationSupport_left_mem_interval
import Theorems.Thm_F6RotationSupport_right_mem_interval
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
attribute [local simp] F6ConvexWindow.ChainDecomposition.mem_part
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_antichains
attribute [local simp] F6ConvexWindow.mem_ideal


attribute [local simp] F6RotationSupport.mem_supportUnion
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
theorem _root_.solution {alpha beta : R} (hab : alpha < beta) :
    2 ≤ (interval alpha beta).card := by
  have hsub : ({alpha, beta} : Finset R) ⊆ interval alpha beta := by
    intro rho hrho
    rcases mem_insert.mp hrho with rfl | hrho
    · exact left_mem_interval hab.le
    · have heq := mem_singleton.mp hrho
      subst rho
      exact right_mem_interval hab.le
  have hcard := card_le_card hsub
  simpa [hab.ne] using hcard
end F6RotationSupport
