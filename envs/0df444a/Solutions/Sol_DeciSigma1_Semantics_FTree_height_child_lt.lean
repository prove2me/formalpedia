-- Prove2me | solution 1 for DeciSigma1.Semantics.FTree.height_child_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:01:11.407513+00:00
-- url     : https://prove2.me/submissions/cdf65127-201a-4dc8-aed7-92f323b2cf7a

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Theorems.Thm_DeciSigma1_Semantics_FTree_height_node

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.FTree
open DeciSigma1.Constraints DeciSigma1.Constraints.PathBounds DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {Γ : List (LitT n V)}
namespace DeciSigma1.Semantics.FTree
theorem _root_.solution (a : Fin n → FTree n) (i : Fin n) :
    (a i).height < (node a).height := by
  rw [height_node]
  have := Finset.le_sup (f := fun i => (a i).height) (Finset.mem_univ i)
  omega
end DeciSigma1.Semantics.FTree
