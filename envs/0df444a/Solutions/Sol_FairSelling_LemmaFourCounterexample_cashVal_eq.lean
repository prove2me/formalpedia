-- Prove2me | solution 1 for FairSelling.LemmaFourCounterexample.cashVal_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:05:58.727953+00:00
-- url     : https://prove2.me/submissions/683ed692-69dc-40ff-a412-85e8274bf3d2

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
theorem _root_.solution (x : Option (Fin 6)) : cashVal R w x = (cwn x : ℝ) := by
  cases x with
  | none => simp [cwn]
  | some g => by_cases hg : g ∈ R <;> simp [cwn, restrictVal, hg, w]
end FairSelling.LemmaFourCounterexample
