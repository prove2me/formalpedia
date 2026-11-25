-- Prove2me | solution 1 for F6ConvexWindow.antichain_inc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:31:46.906798+00:00
-- url     : https://prove2.me/submissions/1ed572c5-4aa7-4345-9fc7-2ae95f2770ce

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
theorem _root_.solution {s : Finset V} (h : Antichain s)
    {x y : V} (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) : IncRel x y :=
  ⟨fun hxy => hne (h x hx y hy hxy), fun hyx => hne (h y hy x hx hyx).symm⟩
end F6ConvexWindow
