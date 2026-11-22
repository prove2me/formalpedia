-- Prove2me | solution 1 for DeciSigma1.Semantics.FTree.height_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:00:03.77536+00:00
-- url     : https://prove2.me/submissions/4beba3bf-98e1-47e0-a062-e24dfe218294

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
theorem _root_.solution (a : Fin n → FTree n) :
    (node a).height = (Finset.univ.sup fun i => (a i).height) + 1 := rfl
end DeciSigma1.Semantics.FTree
