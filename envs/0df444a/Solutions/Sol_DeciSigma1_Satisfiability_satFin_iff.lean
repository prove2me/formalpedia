-- Prove2me | solution 1 for DeciSigma1.Satisfiability.satFin_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:05:51.8138+00:00
-- url     : https://prove2.me/submissions/c8212999-1f86-4a79-bb0a-8d77f1765399

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Theorems.Thm_DeciSigma1_Satisfiability_CycleClash_no_finite_solution
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_depth
public import Theorems.Thm_DeciSigma1_Satisfiability_satFin_of_leastShape_depth
public import Theorems.Thm_DeciSigma1_Constraints_LabelClash_unsatisfiable


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {Γ : List (LitT n V)}
omit [Fintype V]
namespace DeciSigma1.Satisfiability
theorem _root_.solution [Finite V] : (∃ σ : V → FTree n, Covariant.Sat (FTree.toTree ∘ σ) Γ) ↔
    ¬ LabelClash Γ ∧ ¬ CycleClash Γ := by
  classical
  let := Fintype.ofFinite V
  constructor
  · intro hfin
    obtain ⟨σ, hσ⟩ := hfin
    exact ⟨fun hl => hl.unsatisfiable ⟨FTree.toTree ∘ σ, hσ⟩,
      fun hc => hc.no_finite_solution ⟨σ, hσ⟩⟩
  · rintro ⟨hl, hc⟩
    exact satFin_of_leastShape_depth hl (leastShape_depth hc)
end DeciSigma1.Satisfiability
