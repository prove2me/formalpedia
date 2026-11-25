-- Prove2me | solution 1 for GalvinMultigraph.Local.degROn_sdiff_covered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:03:04.726598+00:00
-- url     : https://prove2.me/submissions/fbb71662-8b92-4d49-b479-e71801a1bf55

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
omit [Fintype U] [Fintype R] [Fintype E] [DecidableEq U]
namespace GalvinMultigraph.Local
theorem _root_.solution (left : E → U) (right : E → R) (S M : Finset E)
    (hM : IsMatchingOn left right M) (hMS : M ⊆ S) {m : E} (hm : m ∈ M) :
    degROn right S (right m) = degROn right (S \ M) (right m) + 1 := by
  classical
  have hkey : (S \ M).filter (fun e => right e = right m)
      = (S.filter (fun e => right e = right m)).erase m := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hxS, hxM⟩, hx⟩
      exact ⟨fun h => hxM (h ▸ hm), hxS, hx⟩
    · rintro ⟨hxm, hxS, hx⟩
      refine ⟨⟨hxS, ?_⟩, hx⟩
      intro hxM
      exact (hM x hxM m hm hxm).2 (by rw [hx])
  have hmem : m ∈ S.filter (fun e => right e = right m) := Finset.mem_filter.mpr ⟨hMS hm, rfl⟩
  have hpos : 0 < (S.filter (fun e => right e = right m)).card := Finset.card_pos.mpr ⟨m, hmem⟩
  unfold degROn
  rw [hkey, Finset.card_erase_of_mem hmem]
  omega
end GalvinMultigraph.Local
