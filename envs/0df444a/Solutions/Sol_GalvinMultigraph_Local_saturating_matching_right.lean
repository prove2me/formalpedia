-- Prove2me | solution 1 for GalvinMultigraph.Local.saturating_matching_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:07:22.473801+00:00
-- url     : https://prove2.me/submissions/f3251aca-dc5c-4095-94b6-f01378a03df7

module
public import Definitions.Def_GalvinMultigraph_Local_Stable
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Set
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Definitions.Def_GalvinMultigraph_Local_Konig
public import Theorems.Thm_GalvinMultigraph_Local_saturating_matching_left

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
theorem _root_.solution (left : E → U) (right : E → R) (S : Finset E) (Δ : ℕ) (hΔ : 0 < Δ)
    (hL : ∀ u, degLOn left S u ≤ Δ) :
    ∃ M : Finset E, M ⊆ S ∧ IsMatchingOn left right M ∧
      ∀ r, degROn right S r = Δ → ∃ e ∈ M, right e = r := by
  obtain ⟨M, hMS, hM, hsat⟩ := saturating_matching_left right left S Δ hΔ (fun u => hL u)
  exact ⟨M, hMS, fun e he f hf hne => ⟨(hM e he f hf hne).2, (hM e he f hf hne).1⟩, hsat⟩
end GalvinMultigraph.Local
