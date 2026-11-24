-- Prove2me | solution 1 for FairSelling.preliminary_stage_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:10:39.008267+00:00
-- url     : https://prove2.me/submissions/0c52a3b3-b225-4947-8395-085805a563d0

import Mathlib
import Definitions.Def_RequestProject_LemmaFourResidual
import Definitions.Def_RequestProject_PreliminaryPhase
import Theorems.Thm_P2M_FairSelling_MMS2_cash_of_one_good_loss__47c1f0f02fdb
import Theorems.Thm_FairSelling_MMS_nonneg
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
    (i0 : Fin 3) (e : G) (hbig : (3 / 4 : ℝ) * MMS 3 (v i0) p ≤ p e) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  classical
  obtain ⟨a, -, hmin⟩ := Finset.exists_min_image (f := fun i => MMS 3 (v i) p)
    (Finset.univ : Finset (Fin 3)) ⟨0, Finset.mem_univ 0⟩
  obtain ⟨b, d, hba, hda, hbd⟩ := fin3_others a
  have hma0 : 0 ≤ (3 / 4 : ℝ) * MMS 3 (v a) p := by
    have := MMS_nonneg (n := 3) (by norm_num) (v a) p (hv a) hp
    linarith
  have hmae : (3 / 4 : ℝ) * MMS 3 (v a) p ≤ p e := by
    have := hmin i0 (Finset.mem_univ i0)
    linarith
  have hunion : (∅ : Finset G) ∪ ({e} : Finset G) = {e} := Finset.empty_union _
  have hsum : ∑ g ∈ ({e} : Finset G), p g = p e := Finset.sum_singleton _ _
  refine finish_from_cash_reduction v p hv hp a b d (Ne.symm hba) (Ne.symm hda) hbd
    ∅ {e} ((3 / 4 : ℝ) * MMS 3 (v a) p) (p e - (3 / 4 : ℝ) * MMS 3 (v a) p)
    (Finset.disjoint_empty_left _) hma0 (by linarith) (by rw [hsum]; linarith) ?_ ?_ ?_
  · simp [vbarSum]
  · exact MMS2_cash_of_one_good_loss' (v b) p (hv b) hp ∅ {e} e hunion _ _
      (by linarith) hma0 (by linarith [hmin b (Finset.mem_univ b)]) hmae (by linarith)
  · exact MMS2_cash_of_one_good_loss' (v d) p (hv d) hp ∅ {e} e hunion _ _
      (by linarith) hma0 (by linarith [hmin d (Finset.mem_univ d)]) hmae (by linarith)
end FairSelling
