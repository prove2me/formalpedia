-- Prove2me | solution 1 for DeciSigma1.Satisfiability.cycleClashB_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:03:48.671316+00:00
-- url     : https://prove2.me/submissions/59697ccf-af8c-44aa-a4a1-aa5edfeffad3

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Theorems.Thm_DeciSigma1_Satisfiability_cycleClashB_iff_bounded

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
namespace DeciSigma1.Satisfiability
theorem _root_.solution {Γ : List (LitT n V)} (h : cycleClashB Γ = true) :
    CycleClash Γ := by
  obtain ⟨ρ, x, y, hp, _, hl, hd, hu⟩ := (cycleClashB_iff_bounded Γ).mp h
  exact ⟨ρ, x, y, List.ne_nil_of_length_pos hp, hl, hd, hu⟩
end DeciSigma1.Satisfiability
