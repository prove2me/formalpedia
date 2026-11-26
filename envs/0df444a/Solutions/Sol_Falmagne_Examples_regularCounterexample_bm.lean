-- Prove2me | solution 1 for Falmagne.Examples.regularCounterexample_bm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:41.35652+00:00
-- url     : https://prove2.me/submissions/fce23a64-25e8-47c9-9bb2-5c03a6e56918

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_Examples_regularCounterexampleQ_bm

set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof
namespace Falmagne.Examples
theorem _root_.solution :
    blockMarschak regularCounterexample (0 : Fin 4) {0} = -1 / 2 := by
  unfold blockMarschak upperMobius regularCounterexample
  have h := congrArg (fun q : ℚ => (q : ℝ)) regularCounterexampleQ_bm
  push_cast at h
  exact h
end Falmagne.Examples
