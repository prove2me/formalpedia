-- Prove2me | solution 1 for FairSelling.preliminary_stage_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:10:59.591169+00:00
-- url     : https://prove2.me/submissions/adf5a67d-8ece-43c9-af2e-8196093091a2

import Mathlib
import Definitions.Def_RequestProject_LemmaFourResidual
import Definitions.Def_RequestProject_PreliminaryPhase
import Theorems.Thm_P2M_FairSelling_MMS2_cash_of_one_good_loss__47c1f0f02fdb
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_fin3_others
import Theorems.Thm_FairSelling_finish_from_cash_reduction
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
namespace FairSelling
theorem _root_.solution (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hcheap : ∀ i g, p g < (3 / 4 : ℝ) * MMS 3 (v i) p)
    (a : Fin 3) (e : G) (hbig : (3 / 4 : ℝ) * MMS 3 (v a) p ≤ v a e) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  classical
  obtain ⟨b, d, hba, hda, hbd⟩ := fin3_others a
  have hunion : ({e} : Finset G) ∪ (∅ : Finset G) = {e} := Finset.union_empty _
  refine finish_from_cash_reduction v p hv hp a b d (Ne.symm hba) (Ne.symm hda) hbd
    {e} ∅ 0 0 (Finset.disjoint_empty_right _) le_rfl le_rfl (by simp) ?_ ?_ ?_
  · simp only [vbarSum, Finset.sum_singleton, vbar, add_zero]
    exact le_trans hbig (le_max_right _ _)
  · exact MMS2_cash_of_one_good_loss' (v b) p (hv b) hp {e} ∅ e hunion 0 (p e) le_rfl (hp e)
      (hcheap b e).le le_rfl (by linarith)
  · exact MMS2_cash_of_one_good_loss' (v d) p (hv d) hp {e} ∅ e hunion 0 (p e) le_rfl (hp e)
      (hcheap d e).le le_rfl (by linarith)
end FairSelling
