-- Prove2me | solution 1 for GalvinMultigraph.Local.degLOn_sdiff_uncovered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:03:06.793565+00:00
-- url     : https://prove2.me/submissions/1e7f80c5-d2a5-488e-8a31-a22fc29c2978

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
omit [Fintype U] [Fintype E]
namespace GalvinMultigraph.Local
theorem _root_.solution (left : E → U) (S M : Finset E) (u : U)
    (h : ∀ m ∈ M, left m ≠ u) : degLOn left (S \ M) u = degLOn left S u := by
  unfold degLOn
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, fun hxM => h x hxM hx.2⟩, hx.2⟩⟩
end GalvinMultigraph.Local
