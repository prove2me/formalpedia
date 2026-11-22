-- Prove2me | solution 1 for DeciSigma1.Satisfiability.satFinB_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:15:53.764096+00:00
-- url     : https://prove2.me/submissions/3b2eeb6b-5e60-4da4-a15b-3083bde6fab5

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Theorems.Thm_DeciSigma1_Satisfiability_Covariant_satFinB_iff
public import Theorems.Thm_DeciSigma1_Satisfiability_satFinite_iff_signed

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Satisfiability.Covariant DeciSigma1.Semantics
open DeciSigma1.Semantics.SignSelection
variable {n : ℕ} {V : Type*} [Fintype V]
variable [DecidableEq V]
namespace DeciSigma1.Satisfiability
theorem _root_.solution (c : Fin n → Bool) (Γ : List (LitT n V)) :
    satFinB c Γ = true ↔ ∃ σ : V → FTree n, SatT c (FTree.toTree ∘ σ) Γ :=
  (Covariant.satFinB_iff _).trans (satFinite_iff_signed c Γ).symm
end DeciSigma1.Satisfiability
