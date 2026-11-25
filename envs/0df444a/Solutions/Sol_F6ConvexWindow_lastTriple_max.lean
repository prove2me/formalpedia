-- Prove2me | solution 1 for F6ConvexWindow.lastTriple_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:37:44.525911+00:00
-- url     : https://prove2.me/submissions/332c87ee-45d1-4b22-a06a-4c9173d32efe

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (F : Finset (Finset V)) (hn : F.Nonempty) :
    ∀ S ∈ F, (ideal S).card ≤ (ideal (lastTriple F hn)).card :=
  (Classical.choose_spec (exists_max_image F (fun T => (ideal T).card) hn)).2
end F6ConvexWindow
