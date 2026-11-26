-- Prove2me | solution 1 for Falmagne.Examples.regularCounterexample_bm_negative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:30:41.346324+00:00
-- url     : https://prove2.me/submissions/72eb0e6c-e6f0-4470-9481-4ec33b8a9cc3

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
public import Theorems.Thm_Falmagne_Examples_regularCounterexample_bm

set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof
namespace Falmagne.Examples
theorem _root_.solution :
    blockMarschak regularCounterexample (0 : Fin 4) {0} < 0 := by
  rw [regularCounterexample_bm]
  norm_num
end Falmagne.Examples
