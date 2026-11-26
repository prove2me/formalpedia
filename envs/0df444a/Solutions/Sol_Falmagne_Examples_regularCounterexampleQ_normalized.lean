-- Prove2me | solution 1 for Falmagne.Examples.regularCounterexampleQ_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:00.566629+00:00
-- url     : https://prove2.me/submissions/27647c66-325f-4bbc-8bff-a41a4944e151

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
    (∀ A x, 0 ≤ regularCounterexampleQ A x) ∧
    (∀ A x, x ∉ A → regularCounterexampleQ A x = 0) ∧
    (∀ A, A.Nonempty → ∑ x ∈ A, regularCounterexampleQ A x = 1) := by
  decide +kernel
end Falmagne.Examples
