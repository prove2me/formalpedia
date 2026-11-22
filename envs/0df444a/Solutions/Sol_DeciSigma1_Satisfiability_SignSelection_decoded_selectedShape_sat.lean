-- Prove2me | solution 1 for DeciSigma1.Satisfiability.SignSelection.decoded_selectedShape_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:01:50.462312+00:00
-- url     : https://prove2.me/submissions/419c5655-4a36-4edd-bed4-79a3a37f0617

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Theorems.Thm_DeciSigma1_Satisfiability_SignSelection_selectedShape_sat
public import Theorems.Thm_DeciSigma1_Satisfiability_SignSelection_selectedShape_fixed
public import Theorems.Thm_DeciSigma1_Constraints_normalized_decoded
public import Theorems.Thm_DeciSigma1_Constraints_sat_iff_signed


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability DeciSigma1.Satisfiability.SignSelection
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
open DeciSigma1.Semantics.SignSelection
variable {n : ℕ} {V : Type*} [Fintype V]
omit [Fintype V]
namespace DeciSigma1.Satisfiability.SignSelection
theorem _root_.solution {c : Fin n → Bool} {Γ : List (LitT n V)}
    (hl : ¬ LabelClash (signed c Γ)) : Constraints.SatT c (decoded c (selectedShape c Γ)) Γ := by
  apply (sat_iff_signed c _ Γ).mpr
  rw [normalized_decoded c (selectedShape_fixed c Γ)]
  exact selectedShape_sat hl
end DeciSigma1.Satisfiability.SignSelection
