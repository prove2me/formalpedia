-- Prove2me | solution 1 for Falmagne.Examples.regularCounterexampleQ_bm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:06.378394+00:00
-- url     : https://prove2.me/submissions/76ffe3c2-8e8d-47f9-9f6f-670a21a50038

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
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Falmagne.Examples
theorem _root_.solution :
    (∑ B ∈ univ.filter (fun B : Finset (Fin 4) => {(0 : Fin 4)} ⊆ B),
      (-1 : ℚ) ^ (B \ {(0 : Fin 4)}).card * regularCounterexampleQ B 0) = -1 / 2 := by
  decide +kernel
end Falmagne.Examples
