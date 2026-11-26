-- Prove2me | solution 1 for Falmagne.Examples.singleton_falmagne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:44.997178+00:00
-- url     : https://prove2.me/submissions/c40ada4e-e85a-4117-b3cc-7b5a01feb72e

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_Examples_singleton_isChoiceRule
public import Theorems.Thm_Falmagne_falmagne_blockMarschak


set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof
namespace Falmagne.Examples
theorem _root_.solution :
    RandomUtilityRepresentable (rankingChoice singletonRanking) ↔
      BlockMarschakNonnegative (rankingChoice singletonRanking) :=
  falmagne_blockMarschak singleton_isChoiceRule
end Falmagne.Examples
