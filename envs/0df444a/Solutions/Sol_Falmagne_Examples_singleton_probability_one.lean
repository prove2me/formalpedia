-- Prove2me | solution 1 for Falmagne.Examples.singleton_probability_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:19.468018+00:00
-- url     : https://prove2.me/submissions/68c7356b-b3f3-4413-8dc5-7d412ad3fe74

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples

set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof
namespace Falmagne.Examples
theorem _root_.solution :
    rankingChoice singletonRanking {(0 : Fin 1)} 0 = 1 := by
  norm_num [rankingChoice, lowerContour, singletonRanking]
end Falmagne.Examples
