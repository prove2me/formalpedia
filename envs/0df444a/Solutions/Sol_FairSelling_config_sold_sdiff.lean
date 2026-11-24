-- Prove2me | solution 1 for FairSelling.config_sold_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:07:32.692684+00:00
-- url     : https://prove2.me/submissions/6cb1c503-42d6-41f0-8fec-b7a99fb22d5d

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
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



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {A : Fin 3 → Finset G} {s : Finset G} {q : Fin 3 → ℝ} {r : ℝ}
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hcfg : ConfigN 3 w p r A s q) (X : Finset G) :
    ∑ g ∈ s \ X, p g = (∑ i, q i) - ∑ g ∈ s ∩ X, p g := by
  have h : s \ X = s \ (s ∩ X) := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  rw [h, Finset.sum_sdiff_eq_sub Finset.inter_subset_left, hcfg.2.2.2.2.1]
end FairSelling
