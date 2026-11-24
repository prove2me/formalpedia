-- Prove2me | solution 1 for FairSelling.remove_one_cash_MMS2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:47:22.794246+00:00
-- url     : https://prove2.me/submissions/89c5ff35-dc88-47f6-b68f-8f10e0b714e4

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_ThreeAgentCash
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_nonneg
import Theorems.Thm_FairSelling_cashPrice_nonneg
import Theorems.Thm_FairSelling_exists_reduced_three
import Theorems.Thm_FairSelling_le_MMS_of_outcome
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_restrictVal_nonneg
import Theorems.Thm_FairSelling_unifiedOutcome_valid
import Theorems.Thm_FairSelling_util_unifiedOutcome
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
    (g : G) :
    MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ {g}) w)
      (cashPrice (Finset.univ \ {g}) p (p g)) := by
  obtain ⟨A, s, q, hcfg, hs⟩ := exists_reduced_three w p hw hp;
  obtain ⟨lost, j, k, hlj, hlk, hjk, hg⟩ : ∃ lost j k : Fin 3, lost ≠ j ∧ lost ≠ k ∧ j ≠ k ∧ g ∈ s ∨ ∃ lost j k : Fin 3, lost ≠ j ∧ lost ≠ k ∧ j ≠ k ∧ g ∈ A lost := by
    by_cases hg : g ∈ s <;> simp_all +decide [ ConfigN ];
    · exact ⟨ 0, 1, 2, Or.inl ⟨ by decide, by decide, by decide ⟩ ⟩;
    · simp_all +decide [ Finset.ext_iff ];
      obtain ⟨ i, hi ⟩ := hcfg.2.2.1 g |>.resolve_left hg; use i; fin_cases i <;> simp_all +decide ;
  · have h_outcome : ∃ o : Outcome (Option G) 2, o.Valid (cashPrice (Finset.univ \ {g}) p (p g)) ∧ util (cashVal (Finset.univ \ {g}) w) o 0 ≥ vbarSum w p (A j) + q j ∧ util (cashVal (Finset.univ \ {g}) w) o 1 ≥ vbarSum w p (A k) + q k := by
      refine' ⟨ unifiedOutcome ( fun i => cashVal ( Finset.univ \ { g } ) w ) ( cashPrice ( Finset.univ \ { g } ) p ( p g ) ) ( fun i => if i = 0 then Finset.map ( Function.Embedding.some ) ( A j ) else Finset.map ( Function.Embedding.some ) ( A k ) ) ( Finset.map ( Function.Embedding.some ) ( s \ { g } ) ∪ { none } ) ( fun i => if i = 0 then q j else q k ), _, _, _ ⟩ <;> simp +decide [ unifiedOutcome_valid, util_unifiedOutcome ];
      · refine' unifiedOutcome_valid _ _ _ _ _ _ _ _ _ _;
        · exact fun x => cashPrice_nonneg _ _ hp _ ( hp g ) x;
        · simp +decide [ Fin.forall_fin_two, Finset.disjoint_left ];
          exact ⟨ fun a ha hb => Finset.disjoint_left.mp ( hcfg.1 j k hjk ) ha hb, fun a ha hb => Finset.disjoint_left.mp ( hcfg.1 k j ( Ne.symm hjk ) ) ha hb ⟩;
        · have := hcfg.2.1; simp_all +decide [ Finset.disjoint_left ] ;
          grind;
        · exact fun i => by split_ifs <;> [ exact hcfg.2.2.2.1 j; exact hcfg.2.2.2.1 k ] ;
        · have := hcfg.2.2.2.2.1; simp_all +decide [ Fin.sum_univ_three ] ;
          unfold restrictVal; simp +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', * ] ;
          fin_cases j <;> fin_cases k <;> fin_cases lost <;> simp +decide at hlj hlk hjk ⊢ <;> linarith! [ hcfg.2.2.2.1 0, hcfg.2.2.2.1 1, hcfg.2.2.2.1 2 ];
      · apply Eq.ge
        rw [util_unifiedOutcome (fun _ => cashVal (Finset.univ \ {g}) w) (cashPrice (Finset.univ \ {g}) p (p g)) (fun i => if i = 0 then Finset.map Function.Embedding.some (A j) else Finset.map Function.Embedding.some (A k)) (insert none (Finset.map Function.Embedding.some (s \ {g}))) (fun i => if i = 0 then q j else q k) 0]
        simp only [↓reduceIte, vbarSum, Finset.sum_map, Function.Embedding.some_apply]
        congr 1
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxg : x ≠ g := fun h => by subst h; exact Finset.disjoint_left.mp (hcfg.2.1 j) hg hx
        simp [vbar, cashVal, cashPrice, restrictVal, hxg]
      · apply Eq.ge
        rw [util_unifiedOutcome (fun _ => cashVal (Finset.univ \ {g}) w) (cashPrice (Finset.univ \ {g}) p (p g)) (fun i => if i = 0 then Finset.map Function.Embedding.some (A j) else Finset.map Function.Embedding.some (A k)) (insert none (Finset.map Function.Embedding.some (s \ {g}))) (fun i => if i = 0 then q j else q k) 1]
        simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, vbarSum, Finset.sum_map, Function.Embedding.some_apply]
        congr 1
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxg : x ≠ g := fun h => by subst h; exact Finset.disjoint_left.mp (hcfg.2.1 k) hg hx
        simp [vbar, cashVal, cashPrice, restrictVal, hxg]
    obtain ⟨ o, ho₁, ho₂, ho₃ ⟩ := h_outcome;
    have h_outcome : ∀ i, util (cashVal (Finset.univ \ {g}) w) o i ≥ MMS 3 w p := by
      intro i
      fin_cases i <;> simp_all +decide [ ConfigN ];
      · linarith [ hcfg.2.2.2.2.2 j ];
      · linarith [ hcfg.2.2.2.2.2 k ];
    apply le_MMS_of_outcome;
    any_goals assumption;
    · decide +revert;
    · exact cashVal_nonneg _ _ hw;
    · exact fun x => by cases x <;> [ exact hp g; exact restrictVal_nonneg _ ( fun _ => hp _ ) _ ] ;
  · obtain ⟨lost, j, k, hlj, hlk, hjk, hg⟩ : ∃ lost j k : Fin 3, lost ≠ j ∧ lost ≠ k ∧ j ≠ k ∧ g ∈ A lost ∧ s ∩ {g} = ∅ := by
      have := hcfg.2.1;
      obtain ⟨ lost, j, k, hlj, hlk, hjk, hg ⟩ := ‹∃ lost j k, lost ≠ j ∧ lost ≠ k ∧ j ≠ k ∧ g ∈ A lost›; use lost, j, k; simp_all +decide [ Finset.disjoint_left ] ;
      exact Finset.disjoint_iff_inter_eq_empty.mp ( Finset.disjoint_singleton_right.mpr fun h => this lost h hg );
    obtain ⟨o, ho_valid, ho_util⟩ : ∃ o : Outcome (Option G) 2, o.Valid (cashPrice (Finset.univ \ {g}) p (p g)) ∧ ∀ i, MMS 3 w p ≤ util (cashVal (Finset.univ \ {g}) w) o i := by
      refine' ⟨ _, _, _ ⟩;
      refine' unifiedOutcome ( fun i => cashVal ( Finset.univ \ { g } ) w ) ( cashPrice ( Finset.univ \ { g } ) p ( p g ) ) ( fun i => Finset.map ( Function.Embedding.some ) ( A ( if i = 0 then j else k ) ) ) ( Finset.map ( Function.Embedding.some ) s ) ( fun i => q ( if i = 0 then j else k ) );
      · refine' unifiedOutcome_valid _ _ _ _ _ _ _ _ _ _;
        · exact fun x => cashPrice_nonneg _ _ hp _ ( hp g ) x;
        · simp +decide [ Fin.forall_fin_two, Finset.disjoint_left ];
          exact ⟨ fun a ha hb => Finset.disjoint_left.mp ( hcfg.1 j k hjk ) ha hb, fun a ha hb => Finset.disjoint_left.mp ( hcfg.1 k j ( Ne.symm hjk ) ) ha hb ⟩;
        · have := hcfg.2.1; simp_all +decide [ Finset.disjoint_left ] ;
        · exact fun i => hcfg.2.2.2.1 _;
        · have := hcfg.2.2.2.2.1; simp_all +decide [ Fin.sum_univ_three ] ;
          have h_sum_restrict : ∑ x ∈ s, restrictVal (Finset.univ \ {g}) p x = ∑ x ∈ s, p x := by
            exact Finset.sum_congr rfl fun x hx => if_pos <| by rw [ Finset.ext_iff ] at hg; specialize hg; have := hg.2 x; aesop;
          fin_cases j <;> fin_cases k <;> fin_cases lost <;> simp +decide at hlj hlk hjk ⊢ <;> linarith! [ hcfg.2.2.2.1 0, hcfg.2.2.2.1 1, hcfg.2.2.2.1 2 ];
      · intro i
        have h_util : util (cashVal (Finset.univ \ {g}) w) (unifiedOutcome (fun i => cashVal (Finset.univ \ {g}) w) (cashPrice (Finset.univ \ {g}) p (p g)) (fun i => Finset.map Function.Embedding.some (A (if i = 0 then j else k))) (Finset.map Function.Embedding.some s) fun i => q (if i = 0 then j else k)) i = vbarSum w p (A (if i = 0 then j else k)) + q (if i = 0 then j else k) := by
          rw [util_unifiedOutcome (fun _ => cashVal (Finset.univ \ {g}) w) (cashPrice (Finset.univ \ {g}) p (p g)) (fun i => Finset.map Function.Embedding.some (A (if i = 0 then j else k))) (Finset.map Function.Embedding.some s) (fun i => q (if i = 0 then j else k)) i]
          simp only [vbarSum, Finset.sum_map, Function.Embedding.some_apply]
          congr 1
          refine Finset.sum_congr rfl fun x hx => ?_
          have hxg : x ≠ g := by
            intro h; subst h
            fin_cases i
            · simp only [↓reduceIte] at hx; exact Finset.disjoint_left.mp (hcfg.1 j lost hlj.symm) hx hg.1
            · simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] at hx; exact Finset.disjoint_left.mp (hcfg.1 k lost hlk.symm) hx hg.1
          simp [vbar, cashVal, cashPrice, restrictVal, hxg]
        have := hcfg.2.2.2.2.2 ( if i = 0 then j else k ) ; aesop;
    apply le_MMS_of_outcome;
    all_goals norm_cast;
    · exact cashVal_nonneg _ _ hw;
    · exact fun x => cashPrice_nonneg _ _ hp _ ( hp g ) x
end FairSelling
