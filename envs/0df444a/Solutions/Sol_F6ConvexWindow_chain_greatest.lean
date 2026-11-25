-- Prove2me | solution 1 for F6ConvexWindow.chain_greatest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:37:52.656232+00:00
-- url     : https://prove2.me/submissions/2c4ab5ca-564e-4158-8607-7abc6171db5d

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
theorem _root_.solution {C : Finset V} (hc : Chain C) (hn : C.Nonempty) :
    ∃ y ∈ C, ∀ x ∈ C, x ≤ y := by
  obtain ⟨y, hy, hmax⟩ := exists_maximal hn
  refine ⟨y, hy, ?_⟩
  intro x hx
  exact (hc x hx y hy).elim id (hmax hx)
end F6ConvexWindow
