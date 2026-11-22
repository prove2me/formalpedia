-- Prove2me | solution 1 for DeciSigma1.Satisfiability.leastShape_depth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:02:41.057122+00:00
-- url     : https://prove2.me/submissions/8ea84901-0969-426d-96c8-6b726bce6d18

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_bounded_cycle_of_long_path

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {Γ : List (LitT n V)}
namespace DeciSigma1.Satisfiability
theorem _root_.solution (hn : ¬ CycleClash Γ) (z : V) (π : List (Fin n))
    (hdom : ((leastShape Γ z).fn π).isSome) : π.length ≤ Fintype.card V * Fintype.card V + 1 := by
  by_contra hlen
  obtain ⟨ρ, x, y, hp, _, hl, hd, hu⟩ :=
    leastShape_bounded_cycle_of_long_path hdom (by omega)
  exact hn ⟨ρ, x, y, List.length_pos_iff.mp hp, hl, hd, hu⟩
end DeciSigma1.Satisfiability
