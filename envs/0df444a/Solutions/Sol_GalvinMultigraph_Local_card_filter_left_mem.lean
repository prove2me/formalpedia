-- Prove2me | solution 1 for GalvinMultigraph.Local.card_filter_left_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:55:55.309049+00:00
-- url     : https://prove2.me/submissions/3e191d6e-b898-44bb-939c-0159e39c9e3f

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
omit [Fintype U] [Fintype E] [DecidableEq E]
namespace GalvinMultigraph.Local
theorem _root_.solution (left : E → U) (S : Finset E) (A : Finset U) :
    (S.filter fun e => left e ∈ A).card = ∑ u ∈ A, degLOn left S u := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := left) (t := A)
    (by intro x hx; exact (Finset.mem_filter.mp hx).2)]
  refine Finset.sum_congr rfl fun u hu => ?_
  unfold degLOn
  congr 1
  ext e
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hu⟩, h.2⟩⟩
end GalvinMultigraph.Local
