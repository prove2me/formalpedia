-- Prove2me | solution 1 for Falmagne.Examples.mixture_falmagne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:32:49.269164+00:00
-- url     : https://prove2.me/submissions/e81e904b-0a4d-404f-88c1-74e32658ff70

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_Examples_mixture_isChoiceRule
public import Theorems.Thm_Falmagne_falmagne_blockMarschak


set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof
namespace Falmagne.Examples
theorem _root_.solution :
    RandomUtilityRepresentable mixtureChoice ↔ BlockMarschakNonnegative mixtureChoice :=
  falmagne_blockMarschak mixture_isChoiceRule
end Falmagne.Examples
