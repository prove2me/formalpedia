-- Prove2me | solution 1 for DeciSigma1.Satisfiability.cycleClashB_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:12:16.701181+00:00
-- url     : https://prove2.me/submissions/4220e780-5fb5-427d-9527-a5920760131c

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Theorems.Thm_DeciSigma1_Satisfiability_cycleClash_iff_bounded
public import Theorems.Thm_DeciSigma1_Satisfiability_cycleClashB_iff_bounded

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
namespace DeciSigma1.Satisfiability
theorem _root_.solution {Γ : List (LitT n V)} (hn : ¬ LabelClash Γ)
    (h : CycleClash Γ) : cycleClashB Γ = true :=
  (cycleClashB_iff_bounded Γ).mpr ((cycleClash_iff_bounded hn).mp h)
end DeciSigma1.Satisfiability
