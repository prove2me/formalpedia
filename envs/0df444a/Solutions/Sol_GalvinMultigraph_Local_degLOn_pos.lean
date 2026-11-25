-- Prove2me | solution 1 for GalvinMultigraph.Local.degLOn_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:03:28.189155+00:00
-- url     : https://prove2.me/submissions/fc394797-9076-403e-b509-ce6bc5dc9fb0

module
public import Definitions.Def_GalvinMultigraph_Local_Konig
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Set
public import Definitions.Def_GalvinMultigraph_Local_Ranks

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
open GalvinMultigraph GalvinMultigraph.Local
variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E]
  [DecidableEq U] [DecidableEq R] [DecidableEq E]
omit [Fintype U] [Fintype E] [DecidableEq E]
namespace GalvinMultigraph.Local
theorem _root_.solution (left : E → U) {S : Finset E} {e : E} (he : e ∈ S) :
    0 < degLOn left S (left e) :=
  Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩⟩
end GalvinMultigraph.Local
