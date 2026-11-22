-- Prove2me | solution 1 for DeciSigma1.Satisfiability.SignSelection.selectedShape_domain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:52:00.748154+00:00
-- url     : https://prove2.me/submissions/2fefcb65-c9f2-4f85-b557-c8752aa330f0

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Theorems.Thm_DeciSigma1_Semantics_SignSelection_select_domain


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability DeciSigma1.Satisfiability.SignSelection
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
open DeciSigma1.Semantics.SignSelection
variable {n : ℕ} {V : Type*} [Fintype V]
omit [Fintype V]
namespace DeciSigma1.Satisfiability.SignSelection
theorem _root_.solution (c : Fin n → Bool) (Γ : List (LitT n V))
    (z : (V × Bool)) (π : List (Fin n)) :
    ((selectedShape c Γ z).fn π).isSome = ((leastShape (signed c Γ) z).fn π).isSome :=
  select_domain _ _ _ _ _
end DeciSigma1.Satisfiability.SignSelection
