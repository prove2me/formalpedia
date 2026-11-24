-- Prove2me | solution 1 for FairSelling.LemmaFourCounterexample.MMS_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:08:15.930317+00:00
-- url     : https://prove2.me/submissions/349acfd2-b293-4425-a015-357775c7042f

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity
import Theorems.Thm_FairSelling_LemmaFourCounterexample_hw
import Theorems.Thm_FairSelling_LemmaFourCounterexample_hp
import Theorems.Thm_FairSelling_LemmaFourCounterexample_vbar_eq
import Theorems.Thm_FairSelling_LemmaFourCounterexample_parts_sum
import Theorems.Thm_FairSelling_LemmaFourCounterexample_parts_disjoint
import Theorems.Thm_FairSelling_LemmaFourCounterexample_vbarSum_univ
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_le_MMS_of_outcome
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_three_MMS_le_vbarSum_univ
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
theorem _root_.solution : MMS 3 w p = 50 := by
  refine le_antisymm ?_ ?_
  · have h := three_MMS_le_vbarSum_univ w p hw hp
    rw [vbarSum_univ] at h
    linarith
  · refine le_MMS_of_outcome (by norm_num) w p hw hp ⟨∅, parts, fun _ => 0⟩ ?_ 50 ?_
    · exact ⟨fun j => by simp, parts_disjoint, fun _ => le_refl 0, by simp⟩
    · intro j
      have hj : ∑ g ∈ parts j, w g = ((∑ g ∈ parts j, wn g : ℕ) : ℝ) := by
        simp only [w]; push_cast; rfl
      simp only [util, hj, parts_sum j]
      norm_num
end FairSelling.LemmaFourCounterexample
