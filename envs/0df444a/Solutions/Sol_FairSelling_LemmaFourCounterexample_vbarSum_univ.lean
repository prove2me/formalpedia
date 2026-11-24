-- Prove2me | solution 1 for FairSelling.LemmaFourCounterexample.vbarSum_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:06:27.919165+00:00
-- url     : https://prove2.me/submissions/7d3bb296-2f8a-4eb3-b6ab-12ac5df9bcf9

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity
import Theorems.Thm_FairSelling_LemmaFourCounterexample_vbar_eq
import Theorems.Thm_FairSelling_LemmaFourCounterexample_wn_sum
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
theorem _root_.solution : vbarSum w p Finset.univ = 150 := by
  have : vbarSum w p Finset.univ = ((∑ g, wn g : ℕ) : ℝ) := by
    simp only [vbarSum, vbar_eq, w]
    push_cast
    rfl
  rw [this, wn_sum]
  norm_num
end FairSelling.LemmaFourCounterexample
