-- Prove2me | solution 1 for DeciSigma1.Semantics.FTree.height_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:52:07.625372+00:00
-- url     : https://prove2.me/submissions/5bf80ef1-56e5-4eb2-8f31-a234c0480b11

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.FTree
open DeciSigma1.Constraints DeciSigma1.Constraints.PathBounds DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {Γ : List (LitT n V)}
namespace DeciSigma1.Semantics.FTree
theorem _root_.solution : (top : FTree n).height = 0 := rfl
end DeciSigma1.Semantics.FTree
