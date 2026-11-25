-- Prove2me | solution 1 for F6ConvexWindow.chain_inc_union_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:42:28.33225+00:00
-- url     : https://prove2.me/submissions/8d42b322-02a4-437d-9238-0b542e44e76a

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_Inc
attribute [local simp] F6ConvexWindow.mem_Inc

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution {C : Finset V} (hc : Chain C) :
    Disjoint C (C.biUnion Inc) := by
  classical
  apply disjoint_left.mpr
  intro x hx hxu
  obtain ⟨y, hy, hxy⟩ := mem_biUnion.mp hxu
  have hi := mem_Inc.mp hxy
  exact (hc y hy x hx).elim hi.1 hi.2
end F6ConvexWindow
