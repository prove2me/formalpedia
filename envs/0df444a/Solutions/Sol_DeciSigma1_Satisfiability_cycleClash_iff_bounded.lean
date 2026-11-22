-- Prove2me | solution 1 for DeciSigma1.Satisfiability.cycleClash_iff_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:11:09.177812+00:00
-- url     : https://prove2.me/submissions/f0584737-3848-4e66-a999-33e165e75c00

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Theorems.Thm_DeciSigma1_Satisfiability_CycleClash_no_finite_solution
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_bounded_cycle_of_long_path
public import Theorems.Thm_DeciSigma1_Satisfiability_satFin_of_leastShape_depth

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {Γ : List (LitT n V)}
namespace DeciSigma1.Satisfiability
theorem _root_.solution (hn : ¬ LabelClash Γ) :
    CycleClash Γ ↔ ∃ ρ x y, 0 < ρ.length ∧ ρ.length ≤ Fintype.card V * Fintype.card V ∧
      LowerAt Γ ρ x x ∧ Derives Γ x y ∧ UpperAt Γ ρ y y := by
  constructor
  · intro hc
    by_contra hbounded
    apply hc.no_finite_solution
    apply satFin_of_leastShape_depth hn
    intro z π hdom
    by_contra hlen
    exact hbounded (leastShape_bounded_cycle_of_long_path hdom (by omega))
  · rintro ⟨ρ, x, y, hp, _, hl, hd, hu⟩
    exact ⟨ρ, x, y, List.length_pos_iff.mp hp, hl, hd, hu⟩
end DeciSigma1.Satisfiability
