-- Prove2me | solution 1 for Falmagne.Examples.forwardRanking_isRanking
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:28:44.661325+00:00
-- url     : https://prove2.me/submissions/9b94cf64-7071-4d28-bfe9-bdfca9e1ac63

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
theorem _root_.solution : IsRanking forwardRanking := by
  constructor <;> decide +kernel
end Falmagne.Examples
