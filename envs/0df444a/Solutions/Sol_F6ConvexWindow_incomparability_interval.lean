-- Prove2me | solution 1 for F6ConvexWindow.incomparability_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:58:49.333113+00:00
-- url     : https://prove2.me/submissions/f2813526-300e-434d-af3f-80d56652cfcd

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
theorem _root_.solution {x a b c : V} (hab : a ≤ b) (hbc : b ≤ c)
    (ha : IncRel x a) (hc : IncRel x c) : IncRel x b := by
  exact ⟨fun h => hc.1 (h.trans hbc), fun h => ha.2 (hab.trans h)⟩
end F6ConvexWindow
