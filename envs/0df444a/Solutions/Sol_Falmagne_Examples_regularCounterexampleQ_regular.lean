-- Prove2me | solution 1 for Falmagne.Examples.regularCounterexampleQ_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:05.871623+00:00
-- url     : https://prove2.me/submissions/324b9029-f534-4cce-aad6-4eff1eb4d044

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
    ∀ A B : Finset (Fin 4), A ⊆ B →
      ∀ x ∈ A, regularCounterexampleQ B x ≤ regularCounterexampleQ A x := by
  decide +kernel
end Falmagne.Examples
