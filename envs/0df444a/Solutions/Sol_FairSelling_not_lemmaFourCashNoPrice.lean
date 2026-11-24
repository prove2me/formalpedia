-- Prove2me | solution 1 for FairSelling.not_lemmaFourCashNoPrice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:49:24.002066+00:00
-- url     : https://prove2.me/submissions/7646f843-f6e7-46b3-8682-1cea02a57bb2

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity
import Theorems.Thm_FairSelling_LemmaFourCounterexample_hw
import Theorems.Thm_FairSelling_LemmaFourCounterexample_hp
import Theorems.Thm_FairSelling_LemmaFourCounterexample_vbar_eq
import Theorems.Thm_FairSelling_LemmaFourCounterexample_MMS_three
import Theorems.Thm_FairSelling_LemmaFourCounterexample_K_disjoint_S
import Theorems.Thm_FairSelling_LemmaFourCounterexample_MMS_two_le
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
open LemmaFourCounterexample
namespace FairSelling
theorem _root_.solution : ¬ LemmaFourCashNoPrice (Fin 6) := by
  intro h
  have hnobig : ∀ g, vbar w p g < (3 / 4 : ℝ) * MMS 3 w p := by
    intro g
    rw [MMS_three, vbar_eq]
    have : w g ≤ 37 := by
      simp only [w]
      have : wn g ≤ 37 := by fin_cases g <;> decide
      exact_mod_cast this
    linarith
  have hKval : vbarSum w p K + 0 ≤ (3 / 4 : ℝ) * MMS 3 w p := by
    rw [MMS_three]
    have : vbarSum w p K = 37 := by
      simp only [vbarSum, K, Finset.sum_singleton, vbar_eq, w]
      norm_num [wn]
    rw [this]
    norm_num
  have hS : (∑ g ∈ S, p g) = 0 := by simp [S, p]
  have hmain := h w p hw hp hnobig K S 0 K_disjoint_S (le_refl 0) (by rw [hS])
    (by decide) (Or.inr rfl) hKval
  rw [MMS_three, hS] at hmain
  have hR : (Finset.univ \ (K ∪ S) : Finset (Fin 6)) = R := rfl
  rw [hR, sub_zero] at hmain
  have hle := MMS_two_le
  norm_num at hmain
  linarith
end FairSelling
