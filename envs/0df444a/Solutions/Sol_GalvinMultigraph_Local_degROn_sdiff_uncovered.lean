-- Prove2me | solution 1 for GalvinMultigraph.Local.degROn_sdiff_uncovered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:03:19.427449+00:00
-- url     : https://prove2.me/submissions/92aea418-a974-4dfc-8e46-21554326e4a9

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
omit [Fintype R] [Fintype E]
namespace GalvinMultigraph.Local
theorem _root_.solution (right : E → R) (S M : Finset E) (v : R)
    (h : ∀ m ∈ M, right m ≠ v) : degROn right (S \ M) v = degROn right S v := by
  unfold degROn
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, fun hxM => h x hxM hx.2⟩, hx.2⟩⟩
end GalvinMultigraph.Local
