-- Prove2me | solution 1 for DeciSigma1.Semantics.FiniteMedian.median_toTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:26:14.387783+00:00
-- url     : https://prove2.me/submissions/1b5ba431-d36a-49a8-9ca8-be30019b7272

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Median
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_FiniteMedian
public import Theorems.Thm_DeciSigma1_Semantics_FiniteMedian_extendedLabel_median

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.FiniteMedian
open DeciSigma1.Semantics.Tree
variable {n : ℕ}
namespace DeciSigma1.Semantics.FiniteMedian
theorem _root_.solution (a b c : FTree n) :
    (median a b c).toTree = treeMedian a.toTree b.toTree c.toTree := by
  apply extendedLabel_injective
  funext w
  rw [extendedLabel_median, extendedLabel_treeMedian]
end DeciSigma1.Semantics.FiniteMedian
