-- Prove2me | solution 1 for FairSelling.LemmaFourCounterexample.cashPrice_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:06:06.24574+00:00
-- url     : https://prove2.me/submissions/337ef4a5-7c8f-493a-9cb9-bb84717df285

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity
import Theorems.Thm_FairSelling_LemmaFourCounterexample_vbar_eq
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem


attribute [local simp] FairSelling.LemmaFourCounterexample.vbar_eq

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.LemmaFourCounterexample
namespace FairSelling.LemmaFourCounterexample
theorem _root_.solution (x : Option (Fin 6)) : cashPrice R p 0 x = 0 := by
  cases x with
  | none => simp
  | some g => by_cases hg : g ∈ R <;> simp [restrictVal, hg, p]
end FairSelling.LemmaFourCounterexample
