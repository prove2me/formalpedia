-- Prove2me | solution 1 for DeciSigma1.Satisfiability.SignSelection.selectedShape_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:00:22.152011+00:00
-- url     : https://prove2.me/submissions/6a0b25d4-7ca1-41f4-86ae-ab0947d90c10

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_sat
public import Theorems.Thm_DeciSigma1_Semantics_SignSelection_select_sat


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability DeciSigma1.Satisfiability.SignSelection
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
open DeciSigma1.Semantics.SignSelection
variable {n : ℕ} {V : Type*} [Fintype V]
omit [Fintype V]
namespace DeciSigma1.Satisfiability.SignSelection
theorem _root_.solution {c : Fin n → Bool} {Γ : List (LitT n V)}
    (hl : ¬ LabelClash (signed c Γ)) : Covariant.Sat (selectedShape c Γ) (signed c Γ) :=
  select_sat (leastShape_sat hl) _
end DeciSigma1.Satisfiability.SignSelection
