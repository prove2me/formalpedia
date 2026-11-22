-- Prove2me | solution 1 for DeciSigma1.Satisfiability.SignSelection.selectedShape_depth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:04:02.144006+00:00
-- url     : https://prove2.me/submissions/717f8f11-1009-440d-8433-673b7f9e06cb

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_depth
public import Theorems.Thm_DeciSigma1_Semantics_SignSelection_select_depth


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability DeciSigma1.Satisfiability.SignSelection
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
open DeciSigma1.Semantics.SignSelection
variable {n : ℕ} {V : Type*} [Fintype V]
namespace DeciSigma1.Satisfiability.SignSelection
theorem _root_.solution {c : Fin n → Bool} {Γ : List (LitT n V)}
    (hc : ¬ CycleClash (signed c Γ)) (z : (V × Bool)) (π : List (Fin n))
    (hπ : ((selectedShape c Γ z).fn π).isSome) :
    π.length ≤ Fintype.card (V × Bool) * Fintype.card (V × Bool) + 1 :=
  select_depth c _ _ (leastShape_depth hc) z π hπ
end DeciSigma1.Satisfiability.SignSelection
