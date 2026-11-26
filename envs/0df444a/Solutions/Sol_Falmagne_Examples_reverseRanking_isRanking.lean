-- Prove2me | solution 1 for Falmagne.Examples.reverseRanking_isRanking
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:30.938884+00:00
-- url     : https://prove2.me/submissions/c9377df9-769a-43d4-bcac-93f1c9721d74

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
theorem _root_.solution : IsRanking reverseRanking := by
  constructor <;> decide +kernel
end Falmagne.Examples
