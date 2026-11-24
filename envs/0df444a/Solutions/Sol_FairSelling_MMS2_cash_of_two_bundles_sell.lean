-- Prove2me | solution 1 for FairSelling.MMS2_cash_of_two_bundles_sell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:00:47.032637+00:00
-- url     : https://prove2.me/submissions/30fd9615-def2-4b64-af74-5eb8ea10e732

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
import Theorems.Thm_FairSelling_vbarSum_map_some
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_nonneg
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_nonneg
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_le_MMS_of_outcome
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_unifiedOutcome_valid
import Theorems.Thm_FairSelling_util_unifiedOutcome
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R C D T : Finset G) (c c0 c1 τ : ℝ)
    (hCD : Disjoint C D) (hCT : Disjoint C T) (hDT : Disjoint D T)
    (hCR : C ⊆ R) (hDR : D ⊆ R) (hTR : T ⊆ R)
    (hc : 0 ≤ c) (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (hbudget : c0 + c1 ≤ c + ∑ g ∈ T, p g)
    (hC : τ ≤ vbarSum w p C + c0) (hD : τ ≤ vbarSum w p D + c1) :
    τ ≤ MMS 2 (cashVal R w) (cashPrice R p c) := by
  classical
  set A : Fin 2 → Finset (Option G) :=
    ![C.map Function.Embedding.some, D.map Function.Embedding.some] with hA
  set F : Finset (Option G) := insert none (T.map Function.Embedding.some) with hF
  set q : Fin 2 → ℝ := ![c0, c1] with hq
  have hsumF : ∑ x ∈ F, cashPrice R p c x = c + ∑ g ∈ T, p g := by
    have hnone : none ∉ T.map Function.Embedding.some := by simp
    rw [hF, Finset.sum_insert hnone, cashPrice_none, Finset.sum_map]
    congr 1
    exact Finset.sum_congr rfl (fun g hg => by
      simpa using restrictVal_mem R p (hTR hg))
  refine le_MMS_of_outcome (by norm_num) _ _ (cashVal_nonneg R w hw)
    (cashPrice_nonneg R p hp c hc)
    (unifiedOutcome (fun _ => cashVal R w) (cashPrice R p c) A F q) ?_ τ ?_
  · refine unifiedOutcome_valid _ _ (cashPrice_nonneg R p hp c hc) A F q ?_ ?_ ?_ ?_
    · intro i j hij
      have hmapCD : Disjoint (C.map Function.Embedding.some) (D.map Function.Embedding.some) :=
        (Finset.disjoint_map _).mpr hCD
      fin_cases i <;> fin_cases j <;> simp only [hA] at hij ⊢
      · exact absurd rfl hij
      · exact hmapCD
      · exact hmapCD.symm
      · exact absurd rfl hij
    · intro i
      have hnoneC : none ∉ C.map Function.Embedding.some := by simp
      have hnoneD : none ∉ D.map Function.Embedding.some := by simp
      have hmapTC : Disjoint (T.map Function.Embedding.some) (C.map Function.Embedding.some) :=
        (Finset.disjoint_map _).mpr hCT.symm
      have hmapTD : Disjoint (T.map Function.Embedding.some) (D.map Function.Embedding.some) :=
        (Finset.disjoint_map _).mpr hDT.symm
      fin_cases i <;>
        simp only [hA, hF, Finset.disjoint_insert_left]
      · exact ⟨hnoneC, hmapTC⟩
      · exact ⟨hnoneD, hmapTD⟩
    · intro i; fin_cases i
      · simpa [hq] using hc0
      · simpa [hq] using hc1
    · rw [hsumF, Fin.sum_univ_two]
      simpa [hq] using hbudget
  · intro j
    have hu := util_unifiedOutcome (fun _ : Fin 2 => cashVal R w) (cashPrice R p c) A F q j
    refine le_trans ?_ hu.ge
    fin_cases j
    · simpa [hA, hq, vbarSum_map_some R w p c hCR] using hC
    · simpa [hA, hq, vbarSum_map_some R w p c hDR] using hD
end FairSelling
