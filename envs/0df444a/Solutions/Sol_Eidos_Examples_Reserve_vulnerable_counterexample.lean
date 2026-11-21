-- Prove2me | solution 1 for Eidos.Examples.Reserve.vulnerable_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:37:03.057355+00:00
-- url     : https://prove2.me/submissions/ff70a8f7-1d7a-4f8a-8d95-2f5ee4ff5e81

import Definitions.Def_Eidos_Ergo_Expr
import Definitions.Def_Eidos_Examples_Reserve
import Theorems.Thm_Eidos_Ergo_Long_ofInt_eq_ok_iff
import Theorems.Thm_Eidos_Ergo_Long_sub_eq_ok_iff
attribute [local simp] Eidos.Ergo.Long.ofInt_eq_ok_iff
attribute [local simp] Eidos.Ergo.Long.sub_eq_ok_iff



set_option autoImplicit false
open Eidos Eidos.Examples Eidos.Examples.Reserve
open Ergo
namespace Eidos.Examples.Reserve
theorem _root_.solution :
    Accepts vulnerableScript attackContext ∧
      ¬ WithdrawalBounded exampleReserve attackContext := by
  constructor
  · decide
  · simp [WithdrawalBounded, attackContext, exampleReserve]
end Eidos.Examples.Reserve
