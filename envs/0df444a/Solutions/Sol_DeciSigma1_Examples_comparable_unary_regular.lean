-- Prove2me | solution 1 for DeciSigma1.Examples.comparable_unary_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:31:39.993484+00:00
-- url     : https://prove2.me/submissions/83626e75-018a-499a-a20f-54626e1992dd

module
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Sentences
public import Theorems.Thm_DeciSigma1_Examples_comparable_unary
public import Theorems.Thm_DeciSigma1_booleanSentenceTopFree_regular_iff


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Semantics DeciSigma1.Full.Models
namespace DeciSigma1.Examples
theorem _root_.solution : (comparable 1).HoldsIn IsRegularTree :=
  (DeciSigma1.booleanSentenceTopFree_regular_iff _).mpr comparable_unary
end DeciSigma1.Examples
