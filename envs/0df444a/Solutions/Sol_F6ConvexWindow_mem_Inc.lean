-- Prove2me | solution 1 for F6ConvexWindow.mem_Inc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:31:07.572357+00:00
-- url     : https://prove2.me/submissions/bc04514c-cf48-45cb-b872-e033e6837aa0

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
theorem _root_.solution {x z : V} : z ∈ Inc x ↔ IncRel x z := by
  classical
  simp [Inc]
end F6ConvexWindow
