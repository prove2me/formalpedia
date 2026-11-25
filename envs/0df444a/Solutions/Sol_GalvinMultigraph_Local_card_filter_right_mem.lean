-- Prove2me | solution 1 for GalvinMultigraph.Local.card_filter_right_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:56:26.702276+00:00
-- url     : https://prove2.me/submissions/7b583714-4dbe-4714-af19-415ca7617c68

module
public import Definitions.Def_GalvinMultigraph_Local_Stable
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Set
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Definitions.Def_GalvinMultigraph_Local_Konig

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
theorem _root_.solution (right : E → R) (S : Finset E) (B : Finset R) :
    (S.filter fun e => right e ∈ B).card = ∑ r ∈ B, degROn right S r := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := right) (t := B)
    (by intro x hx; exact (Finset.mem_filter.mp hx).2)]
  refine Finset.sum_congr rfl fun r hr => ?_
  unfold degROn
  congr 1
  ext e
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hr⟩, h.2⟩⟩
end GalvinMultigraph.Local
