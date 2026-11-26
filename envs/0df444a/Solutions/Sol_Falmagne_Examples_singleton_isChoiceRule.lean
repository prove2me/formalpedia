-- Prove2me | solution 1 for Falmagne.Examples.singleton_isChoiceRule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:30:51.998621+00:00
-- url     : https://prove2.me/submissions/2ab49d03-3e35-4b74-8b9d-661d0265d010

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_Examples_singletonLaw_isRankingLaw
public import Theorems.Thm_Falmagne_Examples_singletonLaw_represents
public import Theorems.Thm_Falmagne_represented_isChoiceRule


set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof
namespace Falmagne.Examples
theorem _root_.solution : IsChoiceRule (rankingChoice singletonRanking) :=
  represented_isChoiceRule singletonLaw_isRankingLaw singletonLaw_represents
end Falmagne.Examples
