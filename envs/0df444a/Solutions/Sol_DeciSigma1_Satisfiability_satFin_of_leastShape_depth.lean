-- Prove2me | solution 1 for DeciSigma1.Satisfiability.satFin_of_leastShape_depth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:56:20.3338+00:00
-- url     : https://prove2.me/submissions/579b3001-7b62-4214-b44a-4358dd7c1e77

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_truncate
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_sat


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {Γ : List (LitT n V)}
namespace DeciSigma1.Satisfiability
theorem _root_.solution (hn : ¬ LabelClash Γ)
    (hd : ∀ z π, ((leastShape Γ z).fn π).isSome → π.length ≤ Fintype.card V * Fintype.card V + 1) :
    ∃ σ : V → FTree n, Covariant.Sat (FTree.toTree ∘ σ) Γ := by
  let σ := fun z => FTree.truncate (Fintype.card V * Fintype.card V + 1) (leastShape Γ z)
  have hσ : FTree.toTree ∘ σ = leastShape Γ := by
    funext z
    exact FTree.toTree_truncate (hd z)
  exact ⟨σ, hσ.symm ▸ leastShape_sat hn⟩
end DeciSigma1.Satisfiability
