-- Prove2me | solution 1 for BondySimonovits.exists_minimal_dense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:10:18.624474+00:00
-- url     : https://prove2.me/submissions/e39d6384-d814-46d1-9981-527cdf6de246

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BSBasic
public import Theorems.Thm_BondySimonovits_ecount_le_of_degenerate

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*}
namespace BondySimonovits
theorem _root_.solution (K : SimpleGraph V) [DecidableRel K.Adj] (D : ℕ) (X : Finset V)
    (hX : 2 * D * X.card < ecount K X X + 2 * X.card) :
    ∃ Y ⊆ X, Y.Nonempty ∧ (∀ u ∈ Y, D ≤ (Y.filter (K.Adj u)).card) ∧
      ∀ Y' ⊆ Y, Y'.Nonempty → (∀ u ∈ Y', D ≤ (Y'.filter (K.Adj u)).card) → Y' = Y := by
  classical
  have hex : ∃ Y ⊆ X, Y.Nonempty ∧ (∀ u ∈ Y, D ≤ (Y.filter (K.Adj u)).card) := by
    by_contra hcon
    push Not at hcon
    have := ecount_le_of_degenerate K D X hcon
    omega
  set P := X.powerset.filter
    (fun Y => Y.Nonempty ∧ ∀ u ∈ Y, D ≤ (Y.filter (K.Adj u)).card) with hP
  have hPne : P.Nonempty := by
    obtain ⟨Y, hY, h1, h2⟩ := hex
    exact ⟨Y, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hY, h1, h2⟩⟩
  obtain ⟨Y, hYP, hmin⟩ := Finset.exists_min_image P Finset.card hPne
  simp only [hP, Finset.mem_filter, Finset.mem_powerset] at hYP hmin
  refine ⟨Y, hYP.1, hYP.2.1, hYP.2.2, fun Y' hY' hne hdeg => ?_⟩
  exact Finset.eq_of_subset_of_card_le hY' (hmin Y' ⟨hY'.trans hYP.1, hne, hdeg⟩)
end BondySimonovits
