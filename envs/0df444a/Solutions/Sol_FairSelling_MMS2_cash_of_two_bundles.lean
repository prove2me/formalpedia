-- Prove2me | solution 1 for FairSelling.MMS2_cash_of_two_bundles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:11.429491+00:00
-- url     : https://prove2.me/submissions/9d8d8c78-824e-4250-988b-aa9b002ae3e9

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_ThreeAgentCash
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_nonneg
import Theorems.Thm_FairSelling_cashPrice_nonneg
import Theorems.Thm_FairSelling_le_MMS_of_outcome
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem


attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R C D : Finset G) (c c0 c1 τ : ℝ)
    (hCD : Disjoint C D) (hCR : C ⊆ R) (hDR : D ⊆ R)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hcash : c0 + c1 ≤ c)
    (hC : τ ≤ vbarSum w p C + c0) (hD : τ ≤ vbarSum w p D + c1) :
    τ ≤ MMS 2 (cashVal R w) (cashPrice R p c) := by
  -- Apply the lemma `le_MMS_of_outcome` to the outcome constructed from `C` and `D`.
  have h_outcome : ∃ o : Outcome (Option G) 2, o.Valid (cashPrice R p c) ∧ ∀ j, τ ≤ util (cashVal R w) o j := by
    refine' ⟨ unifiedOutcome ( fun _ => cashVal R w ) ( cashPrice R p c ) ( fun i => if i = 0 then C.map Function.Embedding.some else D.map Function.Embedding.some ) { none } ( fun i => if i = 0 then c0 else c1 ), _, _ ⟩ <;> simp_all +decide [ Outcome.Valid, util ];
    · unfold unifiedOutcome; simp +decide [ Finset.disjoint_left, Finset.disjoint_right ] ;
      refine' ⟨ _, _, _, _ ⟩;
      · grind;
      · exact ⟨ fun a ha ha' b hb hab => False.elim ( Finset.disjoint_left.mp hCD ha ( hab ▸ hb ) ), fun a ha ha' b hb hab => False.elim ( Finset.disjoint_left.mp hCD ( hab ▸ hb ) ha ) ⟩;
      · refine' ⟨ add_nonneg hc0 _, add_nonneg hc1 _ ⟩; all_goals exact Finset.sum_nonneg fun x hx => cashPrice_nonneg R p hp c ( by linarith ) _;
      · simp +decide [ Fin.univ_succ, Finset.sum_biUnion, hCD ];
        rw [ Finset.sum_union ];
        · linarith;
        · simp_all +decide [ Finset.disjoint_left ];
    · convert And.intro hC hD using 2 <;> simp +decide [ vbarSum ];
      · simp +decide [ unifiedOutcome, cashVal, cashPrice ];
        rw [ Finset.sum_filter, Finset.sum_filter ];
        rw [ Finset.sum_map, Finset.sum_map ] ; simp +decide [ vbar ] ; ring;
        simp +decide [ add_comm, add_left_comm, add_assoc, Finset.sum_add_distrib, max_def' ];
        rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun x hx => _ ; split_ifs <;> linarith [ hw x, hp x, show restrictVal R w x = w x from if_pos ( hCR hx ), show restrictVal R p x = p x from if_pos ( hCR hx ) ] ;
      · simp +decide [ unifiedOutcome, cashVal, cashPrice ];
        rw [ Finset.sum_filter, Finset.sum_filter ];
        rw [ Finset.sum_map, Finset.sum_map ] ; simp +decide [ vbar ] ; ring;
        simp +decide [ add_comm, add_left_comm, add_assoc, Finset.sum_add_distrib, max_def' ];
        rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun x hx => _ ; split_ifs <;> linarith [ hw x, hp x, show restrictVal R w x = w x from if_pos ( hDR hx ), show restrictVal R p x = p x from if_pos ( hDR hx ) ] ;
  convert le_MMS_of_outcome ( hn := by decide ) ( cashVal R w ) ( cashPrice R p c ) ( cashVal_nonneg R w hw ) ( cashPrice_nonneg R p hp c ( by linarith ) ) h_outcome.choose h_outcome.choose_spec.1 τ h_outcome.choose_spec.2 using 1
end FairSelling
