-- Prove2me | solution 1 for DeciSigma1.Semantics.FiniteMedian.extendedLabel_toTree_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:03:45.800768+00:00
-- url     : https://prove2.me/submissions/40821ca9-596f-4f4b-b23a-4b2aa4020d4c

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Median
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_FiniteMedian

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.FiniteMedian
open DeciSigma1.Semantics.Tree
variable {n : ℕ}
namespace DeciSigma1.Semantics.FiniteMedian
theorem _root_.solution (t : FTree n) :
    extendedLabel t.toTree [] = rootLabel t := by
  cases t <;> rfl
end DeciSigma1.Semantics.FiniteMedian
