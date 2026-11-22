-- Prove2me | solution 1 for DeciSigma1.Satisfiability.Covariant.satFinB_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:14:32.431158+00:00
-- url     : https://prove2.me/submissions/8a3e2ea9-5182-4a08-a102-6a1534e75132

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Theorems.Thm_DeciSigma1_Satisfiability_satFin_iff
public import Theorems.Thm_DeciSigma1_Satisfiability_Covariant_satFinB_iff_not_clash

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
namespace DeciSigma1.Satisfiability
namespace Covariant
theorem _root_.solution (Γ : List (LitT n V)) :
    satFinB Γ = true ↔ ∃ σ : V → FTree n, Covariant.Sat (FTree.toTree ∘ σ) Γ := by
  rw [satFin_iff, satFinB_iff_not_clash]
end Covariant
end DeciSigma1.Satisfiability
