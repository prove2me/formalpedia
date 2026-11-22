-- Prove2me | solution 1 for DeciSigma1.Satisfiability.sat_iff_signed_not_labelClash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:02:47.724981+00:00
-- url     : https://prove2.me/submissions/70f205f3-3447-403c-98ed-5a8030927107

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Theorems.Thm_DeciSigma1_Satisfiability_SignSelection_decoded_selectedShape_sat
public import Theorems.Thm_DeciSigma1_Constraints_sat_iff_signed
public import Theorems.Thm_DeciSigma1_Satisfiability_satisfiable_iff_not_labelClash


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Satisfiability.Covariant DeciSigma1.Semantics
open DeciSigma1.Semantics.SignSelection
variable {n : ℕ} {V : Type*} [Fintype V]
omit [Fintype V]
namespace DeciSigma1.Satisfiability
theorem _root_.solution (c : Fin n → Bool) (Γ : List (LitT n V)) :
    (∃ ρ, SatT c ρ Γ) ↔ ¬ LabelClash (signed c Γ) := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact satisfiable_iff_not_labelClash.mp ⟨normalized c ρ, (sat_iff_signed c ρ Γ).mp hρ⟩
  · intro h
    exact ⟨decoded c (SignSelection.selectedShape c Γ), SignSelection.decoded_selectedShape_sat h⟩
end DeciSigma1.Satisfiability
