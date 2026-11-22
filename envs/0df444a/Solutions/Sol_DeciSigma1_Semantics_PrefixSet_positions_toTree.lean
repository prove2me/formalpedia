-- Prove2me | solution 1 for DeciSigma1.Semantics.PrefixSet.positions_toTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:56:19.668266+00:00
-- url     : https://prove2.me/submissions/469ec45c-2871-4f80-924a-702152f4b0f5

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
public import Theorems.Thm_DeciSigma1_Semantics_PrefixSet_toTree_fn_eq_f

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
open DeciSigma1.Semantics.PrefixSet
namespace DeciSigma1.Semantics.PrefixSet
theorem _root_.solution (P : PrefixSet n) : P.toTree.positions = P :=
  PrefixSet.ext (Set.ext fun π => toTree_fn_eq_f P π)
end DeciSigma1.Semantics.PrefixSet
