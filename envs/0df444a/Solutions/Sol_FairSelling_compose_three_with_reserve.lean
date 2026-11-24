-- Prove2me | solution 1 for FairSelling.compose_three_with_reserve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:58:15.28458+00:00
-- url     : https://prove2.me/submissions/54cb1ec1-5aaf-4590-b22e-3601e7a88145

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_unifiedOutcome_valid
import Theorems.Thm_FairSelling_util_unifiedOutcome
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.restrictVal_mem


attribute [local simp] FairSelling.mem_optionGoods

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (a b d : Fin 3) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (Ka Sa : Finset G) (ma cash : ℝ)
    (hKSa : Disjoint Ka Sa) (hma0 : 0 ≤ ma) (hbudget : ma + cash ≤ ∑ g ∈ Sa, p g)
    (haU : (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma)
    (o2 : Outcome G 2)
    (ho2sold : ∀ i, Disjoint o2.sold (o2.kept i))
    (ho2disj : ∀ i j, i ≠ j → Disjoint (o2.kept i) (o2.kept j))
    (ho2money : ∀ i, 0 ≤ o2.money i)
    (ho2budget : ∑ i, o2.money i ≤
      ∑ g ∈ o2.sold, restrictVal (Finset.univ \ (Ka ∪ Sa)) p g + cash)
    (hb : (3/4 : ℝ) * MMS 3 (v b) p ≤
      util (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v b)) o2 0)
    (hd : (3/4 : ℝ) * MMS 3 (v d) p ≤
      util (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v d)) o2 1) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3/4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  -- Define the sets and cash values for the composition.
  set R : Finset G := Finset.univ \ (Ka ∪ Sa)
  set Bb : Finset G := o2.kept 0 ∩ R
  set Bd : Finset G := o2.kept 1 ∩ R
  set cb := o2.money 0
  set cd := o2.money 1;
  refine' ⟨ unifiedOutcome v p ( fun i ↦ if i = a then Ka else if i = b then Bb else Bd ) ( Sa ∪ ( o2.sold ∩ R ) ) ( fun i ↦ if i = a then ma else if i = b then cb else cd ), _, _ ⟩ <;> simp_all +decide [ Fin.sum_univ_three ];
  · convert unifiedOutcome_valid v p hp ( fun i => if i = a then Ka else if i = b then Bb else Bd ) ( Sa ∪ o2.sold ∩ R ) ( fun i => if i = a then ma else if i = b then cb else cd ) _ _ _ _ using 1;
    · simp_all +decide [ Fin.forall_fin_succ, Finset.disjoint_left ];
      grind;
    · simp_all +decide [ Fin.forall_fin_succ, Finset.disjoint_left ];
      grind;
    · grind;
    · rw [ Fin.sum_univ_three ];
      rw [ Finset.sum_union ];
      · rw [ show ∑ x ∈ o2.sold ∩ R, p x = ∑ x ∈ o2.sold, restrictVal R p x from ?_ ];
        · grind;
        · rw [ ← Finset.sum_subset ( Finset.inter_subset_left ) ];
          any_goals exact Finset.univ;
          · simp +decide [ Finset.sum_ite, restrictVal ];
          · simp +contextual [ Finset.ext_iff ];
      · exact Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_sdiff.mp ( Finset.mem_inter.mp hx' |>.2 ) |>.2 ( Finset.mem_union_right _ hx );
  · intro i
    by_cases hi : i = a ∨ i = b ∨ i = d;
    · rcases hi with ( rfl | rfl | rfl ) <;> simp_all +decide [ util_unifiedOutcome ];
      · split_ifs <;> simp_all +decide [ util ];
        refine' le_trans hb _;
        rw [ ← Finset.sum_subset ( show Bb ⊆ o2.kept 0 from Finset.inter_subset_left ) ];
        · refine' add_le_add _ le_rfl;
          refine' Finset.sum_le_sum fun x hx => _;
          unfold restrictVal vbar; aesop;
        · simp +contextual [ Bb, restrictVal ];
      · split_ifs <;> simp_all +decide [ util ];
        refine' le_trans hd _;
        rw [ ← Finset.sum_subset ( show Bd ⊆ o2.kept 1 from Finset.inter_subset_left ) ];
        · refine' add_le_add _ le_rfl;
          refine' Finset.sum_le_sum fun x hx => _;
          unfold restrictVal vbar; aesop;
        · simp +contextual [ Bd, restrictVal ];
    · fin_cases i <;> fin_cases a <;> fin_cases b <;> fin_cases d <;> trivial
end FairSelling
