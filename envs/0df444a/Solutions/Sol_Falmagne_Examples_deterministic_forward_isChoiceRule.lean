-- Prove2me | solution 1 for Falmagne.Examples.deterministic_forward_isChoiceRule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:10.896082+00:00
-- url     : https://prove2.me/submissions/0c35f606-cf38-4375-b589-91b77f81b0ab

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_Examples_forwardRanking_isRanking
public import Theorems.Thm_Falmagne_rankingChoice_eq_zero_of_not_mem
public import Theorems.Thm_Falmagne_rankingChoice_nonneg
public import Theorems.Thm_Falmagne_sum_rankingChoice


set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof
namespace Falmagne.Examples
theorem _root_.solution : IsChoiceRule (rankingChoice forwardRanking) := by
  refine ⟨rankingChoice_nonneg forwardRanking, ?_, ?_⟩
  · intro A x hx
    exact rankingChoice_eq_zero_of_not_mem hx
  · intro A hA
    exact sum_rankingChoice forwardRanking_isRanking hA
end Falmagne.Examples
