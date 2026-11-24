-- Prove2me | solution 1 for BondySimonovits.ecount_le_of_degenerate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:08:49.260444+00:00
-- url     : https://prove2.me/submissions/64ceab39-9bb3-412c-a42f-4666a5013fea

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BSBasic
public import Theorems.Thm_BondySimonovits_ecount_erase

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*}
namespace BondySimonovits
theorem _root_.solution (K : SimpleGraph V) [DecidableRel K.Adj] (D : ℕ) :
    ∀ X : Finset V, (∀ Y ⊆ X, Y.Nonempty → ∃ u ∈ Y, (Y.filter (K.Adj u)).card < D) →
      ecount K X X + 2 * X.card ≤ 2 * D * X.card := by
  classical
  intro X
  induction X using Finset.strongInduction with
  | H X ih =>
    intro hX
    rcases X.eq_empty_or_nonempty with h | h
    · subst h; simp [ecount]
    obtain ⟨u, hu, hdeg⟩ := hX X subset_rfl h
    have := ih (X.erase u) (Finset.erase_ssubset hu)
      (fun Y hY hne => hX Y (hY.trans (Finset.erase_subset u X)) hne)
    rw [ecount_erase K X u hu]
    have hc := Finset.card_erase_add_one hu
    nlinarith
end BondySimonovits
