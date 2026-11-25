-- Prove2me | solution 1 for GalvinMultigraph.Local.degROn_le_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:58:59.237634+00:00
-- url     : https://prove2.me/submissions/27b63624-6927-4cad-b2f9-74889c71fa41

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
theorem _root_.solution (right : E → R) {S T : Finset E} (h : S ⊆ T) (r : R) :
    degROn right S r ≤ degROn right T r :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)
end GalvinMultigraph.Local
