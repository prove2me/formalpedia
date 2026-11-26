-- Prove2me | solution 1 for Falmagne.Examples.singletonRanking_isRanking
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:10.604598+00:00
-- url     : https://prove2.me/submissions/35dcf5e6-dd21-4637-9197-5e4f95d05f55

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
theorem _root_.solution : IsRanking singletonRanking := by
  constructor <;> decide +kernel
end Falmagne.Examples
