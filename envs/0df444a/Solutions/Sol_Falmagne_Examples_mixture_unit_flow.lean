-- Prove2me | solution 1 for Falmagne.Examples.mixture_unit_flow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:32:49.913793+00:00
-- url     : https://prove2.me/submissions/58205c58-6d03-48b8-bff9-6f5bffbfb0c9

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_Examples_mixture_isChoiceRule
public import Theorems.Thm_Falmagne_Examples_mixture_BM_nonnegative
public import Theorems.Thm_Falmagne_blockMarschak_isFlow


set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof
namespace Falmagne.Examples
theorem _root_.solution : IsFlow (blockMarschak mixtureChoice) 1 :=
  blockMarschak_isFlow mixtureChoice mixture_isChoiceRule mixture_BM_nonnegative
end Falmagne.Examples
