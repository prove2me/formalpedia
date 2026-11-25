-- Prove2me | solution 1 for GalvinMultigraph.Local.degROn_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:04:03.70313+00:00
-- url     : https://prove2.me/submissions/8d467f4f-b53f-42b5-ae70-1dad5af3710f

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
omit [Fintype R] [Fintype E] [DecidableEq E]
namespace GalvinMultigraph.Local
theorem _root_.solution (right : E → R) {S : Finset E} {e : E} (he : e ∈ S) :
    0 < degROn right S (right e) :=
  Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩⟩
end GalvinMultigraph.Local
