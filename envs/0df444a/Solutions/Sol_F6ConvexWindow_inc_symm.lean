-- Prove2me | solution 1 for F6ConvexWindow.inc_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:58:21.55127+00:00
-- url     : https://prove2.me/submissions/d4946a8e-1f3b-469a-8d1a-4110a2354936

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution {x y : V} (h : IncRel x y) : IncRel y x := ⟨h.2, h.1⟩
end F6ConvexWindow
