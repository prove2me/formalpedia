-- Prove2me | solution 1 for GalvinMultigraph.Local.saturated_matching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:11:02.738209+00:00
-- url     : https://prove2.me/submissions/9a1d49d4-333f-45aa-9632-84deab81ba89

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
public import Theorems.Thm_GalvinMultigraph_Local_saturating_matching_right
public import Theorems.Thm_GalvinMultigraph_Local_merge_matchings

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
open GalvinMultigraph GalvinMultigraph.Local
variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E]
  [DecidableEq U] [DecidableEq R] [DecidableEq E]
namespace GalvinMultigraph.Local
theorem _root_.solution (left : E → U) (right : E → R) (S : Finset E) (Δ : ℕ) (hΔ : 0 < Δ)
    (hL : ∀ u, degLOn left S u ≤ Δ) (hR : ∀ r, degROn right S r ≤ Δ) :
    ∃ M : Finset E, M ⊆ S ∧ IsMatchingOn left right M ∧
      (∀ u, degLOn left S u = Δ → ∃ e ∈ M, left e = u) ∧
      (∀ r, degROn right S r = Δ → ∃ e ∈ M, right e = r) := by
  obtain ⟨ML, hMLS, hML, hLsat⟩ := saturating_matching_left left right S Δ hΔ hR
  obtain ⟨MR, hMRS, hMR, hRsat⟩ := saturating_matching_right left right S Δ hΔ hL
  obtain ⟨M, hMS, hM, hcovL, hcovR⟩ := merge_matchings left right S ML MR hMLS hMRS hML hMR
  exact ⟨M, hMS, hM, fun u hu => hcovL u (hLsat u hu), fun r hr => hcovR r (hRsat r hr)⟩
end GalvinMultigraph.Local
