-- Prove2me | solution 1 for Falmagne.Examples.mixture_isChoiceRule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:59.546176+00:00
-- url     : https://prove2.me/submissions/42280e43-b01a-4968-b4e5-fcd51cf6d69d

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_Examples_mixtureLaw_isRankingLaw
public import Theorems.Thm_Falmagne_Examples_mixtureLaw_represents
public import Theorems.Thm_Falmagne_represented_isChoiceRule


set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof
namespace Falmagne.Examples
theorem _root_.solution : IsChoiceRule mixtureChoice :=
  represented_isChoiceRule mixtureLaw_isRankingLaw mixtureLaw_represents
end Falmagne.Examples
