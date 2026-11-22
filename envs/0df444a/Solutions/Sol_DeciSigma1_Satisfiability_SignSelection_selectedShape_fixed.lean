-- Prove2me | solution 1 for DeciSigma1.Satisfiability.SignSelection.selectedShape_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:00:32.227077+00:00
-- url     : https://prove2.me/submissions/9f5b1eb1-3057-4838-9261-2f4caa6531b1

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Theorems.Thm_DeciSigma1_Semantics_SignSelection_select_fixed


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability DeciSigma1.Satisfiability.SignSelection
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
open DeciSigma1.Semantics.SignSelection
variable {n : ℕ} {V : Type*} [Fintype V]
omit [Fintype V]
namespace DeciSigma1.Satisfiability.SignSelection
theorem _root_.solution (c : Fin n → Bool) (Γ : List (LitT n V)) :
    Signed.dual (selectedShape c Γ) = selectedShape c Γ := select_fixed _ _ _
end DeciSigma1.Satisfiability.SignSelection
