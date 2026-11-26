-- Prove2me | solution 1 for Falmagne.Examples.regularCounterexample_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:51.648561+00:00
-- url     : https://prove2.me/submissions/64f4a4a2-f59d-4706-960c-b027fa1b950c

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_Examples_regularCounterexampleQ_regular

set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof
namespace Falmagne.Examples
theorem _root_.solution :
    ∀ A B : Finset (Fin 4), A ⊆ B →
      ∀ x ∈ A, regularCounterexample B x ≤ regularCounterexample A x := by
  intro A B hAB x hx
  unfold regularCounterexample
  exact_mod_cast regularCounterexampleQ_regular A B hAB x hx
end Falmagne.Examples
