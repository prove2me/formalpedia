-- Prove2me | solution 1 for GalvinMultigraph.Local.degLOn_le_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:56:50.674653+00:00
-- url     : https://prove2.me/submissions/8cad59e4-f0f8-4498-b47c-9b077be9b875

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
theorem _root_.solution (left : E → U) {S T : Finset E} (h : S ⊆ T) (u : U) :
    degLOn left S u ≤ degLOn left T u :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)
end GalvinMultigraph.Local
