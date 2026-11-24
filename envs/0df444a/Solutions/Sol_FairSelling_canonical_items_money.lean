-- Prove2me | solution 1 for FairSelling.canonical_items_money
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:01.714797+00:00
-- url     : https://prove2.me/submissions/027b22fe-72b5-4872-8d80-01b811ac830f

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_CanonicalPartition
import Theorems.Thm_FairSelling_greedy_two_bags
import Theorems.Thm_FairSelling_MMS_nonneg
import Theorems.Thm_FairSelling_bagfill
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_vbarSum_sdiff
import Theorems.Thm_FairSelling_vbarSum_union
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
set_option maxHeartbeats 1600000
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hsmall : ∀ g, vbar w p g < (3/4) * MMS 3 w p) (s : Finset G) (hscard : s.card ≤ 2)
    (hP : (2/3) * ((3/4) * MMS 3 w p) < ∑ g ∈ s, p g)
    (hV : 4 * ((3/4) * MMS 3 w p) ≤ vbarSum w p (Finset.univ \ s) + ∑ g ∈ s, p g) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonical w p ((3/4) * MMS 3 w p) kept sold money leftover := by
  by_cases hτ : 0 < (3 / 4) * MMS 3 w p;
  · have hP_lt_2τ : ∑ g ∈ s, p g < 2 * (3 / 4 * MMS 3 w p) := by
      have hP_lt_2τ : ∑ g ∈ s, p g < ∑ g ∈ s, (3 / 4 * MMS 3 w p) := by
        exact Finset.sum_lt_sum_of_nonempty ( Finset.nonempty_of_ne_empty ( by rintro rfl; norm_num at hP; linarith ) ) fun g hg => lt_of_le_of_lt ( le_max_left _ _ ) ( hsmall g );
      exact hP_lt_2τ.trans_le ( by norm_num; nlinarith [ show ( s.card : ℝ ) ≤ 2 by norm_cast ] );
    by_cases hA : ∀ g ∈ Finset.univ \ s, vbar w p g < (2 / 3) * (3 / 4 * MMS 3 w p);
    · by_cases hA1 : 3 * (3 / 4 * MMS 3 w p) ≤ vbarSum w p (Finset.univ \ s);
      · obtain ⟨B1, B2, hB1, hB2, hdisj, hB1_ge, hB2_ge, hB1B2_le⟩ : ∃ B1 B2 : Finset G, B1 ⊆ Finset.univ \ s ∧ B2 ⊆ Finset.univ \ s ∧ Disjoint B1 B2 ∧ (3 / 4 * MMS 3 w p) ≤ vbarSum w p B1 ∧ (3 / 4 * MMS 3 w p) ≤ vbarSum w p B2 ∧ vbarSum w p B1 + vbarSum w p B2 ≤ 3 * (3 / 4 * MMS 3 w p) := by
          have := greedy_two_bags (vbar w p) (fun g => by
            exact le_max_of_le_left ( hp g )) (3 / 4 * MMS 3 w p) hτ (Finset.univ \ s) hA hA1;
          exact this;
        refine' ⟨ fun i => if i = 0 then B1 else if i = 1 then B2 else ( Finset.univ \ s ) \ ( B1 ∪ B2 ), s, fun i => if i = 0 then 0 else if i = 1 then 0 else ∑ g ∈ s, p g, 2, _, _, _, _, _ ⟩ <;> simp +decide [ Fin.forall_fin_succ ];
        · simp_all +decide [ Finset.disjoint_left, Finset.subset_iff ];
          exact fun x hx hx' => hdisj hx' hx;
        · simp_all +decide [ Finset.subset_iff, Finset.disjoint_left ];
          exact ⟨ fun x hx hx' => hB1 hx' hx, fun x hx hx' => hB2 hx' hx ⟩;
        · exact Finset.sum_nonneg fun _ _ => hp _;
        · simp +decide [ Fin.sum_univ_three ];
        · refine ⟨by simpa using hB1_ge, by simpa using hB2_ge, ?_⟩
          have h_rem : vbarSum w p ((Finset.univ \ s) \ (B1 ∪ B2)) =
              vbarSum w p (Finset.univ \ s) - (vbarSum w p B1 + vbarSum w p B2) := by
            rw [vbarSum_sdiff, vbarSum_union]
            · exact hdisj
            · exact Finset.union_subset hB1 hB2
          linarith
      · obtain ⟨B1, hB1⟩ : ∃ B1 ⊆ Finset.univ \ s, (3 / 4 * MMS 3 w p) ≤ ∑ g ∈ B1, vbar w p g ∧ ∑ g ∈ B1, vbar w p g ≤ (5 / 3) * (3 / 4 * MMS 3 w p) := by
          apply bagfill (fun g => vbar w p g) (3 / 4 * MMS 3 w p) ((5 / 3) * (3 / 4 * MMS 3 w p)) (by linarith) (by linarith) (Finset.univ \ s) (by
          grind) (by
          linarith!);
        obtain ⟨c, hc⟩ : ∃ c ∈ Finset.univ \ s, c ∉ B1 := by
          by_cases hB1_eq : B1 = Finset.univ \ s;
          · simp_all +decide [ vbarSum ];
            grind +splitImp;
          · exact Finset.exists_of_ssubset ( lt_of_le_of_ne hB1.1 hB1_eq );
        refine' ⟨ fun k => if k = 0 then B1 else if k = 1 then { c } else Finset.univ \ ( s ∪ B1 ∪ { c } ), s, fun k => if k = 0 then 0 else if k = 1 then 3 / 4 * MMS 3 w p - vbar w p c else ∑ g ∈ s, p g - ( 3 / 4 * MMS 3 w p - vbar w p c ), 2, _, _, _, _, _ ⟩ <;> simp +decide [ Fin.sum_univ_three ];
        · simp +decide [ Fin.forall_fin_succ, Finset.disjoint_left ];
          grind;
        · simp +decide [ Fin.forall_fin_succ, Finset.disjoint_left ];
          grind;
        · intro k; split_ifs <;> norm_num;
          · linarith [ hsmall c ];
          · linarith [ hsmall c, show 0 ≤ vbar w p c from le_max_of_le_left ( hp c ) ];
        · simp_all +decide [ Fin.forall_fin_succ ];
          simp_all +decide [ vbarSum ];
          rw [ Finset.sum_union ];
          · linarith;
          · exact Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_sdiff.mp ( hB1.1 hx' ) |>.2 hx;
    · obtain ⟨a, ha⟩ : ∃ a ∈ Finset.univ \ s, ∀ b ∈ Finset.univ \ s, vbar w p b ≤ vbar w p a := by
        exact Finset.exists_max_image _ _ ( Finset.nonempty_of_ne_empty ( by aesop_cat ) );
      by_cases hB : vbar w p a ≥ (2 / 3) * (3 / 4 * MMS 3 w p) ∧ ∃ b ∈ Finset.univ \ (s ∪ {a}), vbar w p b ≥ (2 / 3) * (3 / 4 * MMS 3 w p);
      · obtain ⟨ b, hb₁, hb₂ ⟩ := hB.2;
        refine' ⟨ fun i => if i = 0 then { a } else if i = 1 then { b } else Finset.univ \ ( s ∪ { a, b } ), s, fun i => if i = 0 then 3 / 4 * MMS 3 w p - vbar w p a else if i = 1 then 3 / 4 * MMS 3 w p - vbar w p b else ∑ g ∈ s, p g - ( 3 / 4 * MMS 3 w p - vbar w p a ) - ( 3 / 4 * MMS 3 w p - vbar w p b ), 2, _, _, _, _, _ ⟩ <;> simp +decide [ Fin.sum_univ_three ];
        · simp +decide [ Fin.forall_fin_succ, Finset.disjoint_left ];
          grind;
        · simp_all +decide [ Fin.forall_fin_succ, Finset.disjoint_left ];
        · grind;
        · refine' ⟨ _, _ ⟩;
          · intro k; fin_cases k <;> simp +decide [ * ] ;
            · simp +decide [ vbarSum ];
            · simp +decide [ vbarSum ];
            · have h_split : vbarSum w p (Finset.univ \ s) = vbarSum w p {a} + vbarSum w p {b} + vbarSum w p (Finset.univ \ (s ∪ {a, b})) := by
                rw [ ← vbarSum_union, ← vbarSum_union ] <;> norm_num;
                · congr with x ; by_cases hx : x = a <;> by_cases hx' : x = b <;> simp_all +decide [ Finset.mem_sdiff ];
                · grind;
              simp_all +decide [ Finset.sum_singleton, vbarSum ];
              linarith;
          · intro k hk; fin_cases k <;> simp +decide at hk ⊢;
      · obtain ⟨B2, hB2⟩ : ∃ B2 ⊆ Finset.univ \ (s ∪ {a}), (3 / 4 * MMS 3 w p) ≤ vbarSum w p B2 ∧ vbarSum w p B2 ≤ (5 / 3) * (3 / 4 * MMS 3 w p) := by
          apply bagfill (vbar w p) (3 / 4 * MMS 3 w p) (5 / 3 * (3 / 4 * MMS 3 w p)) (by linarith) (by linarith) (Finset.univ \ (s ∪ {a})) (by
          grind) (by
          have h_sum : vbarSum w p (Finset.univ \ s) = vbar w p a + vbarSum w p (Finset.univ \ (s ∪ {a})) := by
            rw [ show Finset.univ \ s = { a } ∪ ( Finset.univ \ ( s ∪ { a } ) ) from ?_, vbarSum_union ] <;> norm_num;
            · unfold vbarSum; aesop;
            · grind;
          linarith! [ hsmall a ]);
        refine' ⟨ fun i => if i = 0 then { a } else if i = 1 then B2 else Finset.univ \ ( s ∪ { a } ∪ B2 ), s, fun i => if i = 0 then 3 / 4 * MMS 3 w p - vbar w p a else if i = 1 then 0 else ∑ g ∈ s, p g - ( 3 / 4 * MMS 3 w p - vbar w p a ), 2, _, _, _, _, _ ⟩ <;> simp +decide [ Fin.forall_fin_succ ];
        · simp_all +decide [ Finset.subset_iff, Finset.disjoint_left ];
          exact fun h => hB2.1 h |>.1 rfl;
        · simp_all +decide [ Finset.subset_iff, Finset.disjoint_left ];
          exact fun x hx hx' => hB2.1 hx' |>.2 hx;
        · grind +extAll;
        · simp +decide [ Fin.sum_univ_three ];
        · refine' ⟨ _, hB2.2.1, _ ⟩;
          · simp +decide [ vbarSum ];
          · have hV2 : vbarSum w p (Finset.univ \ (s ∪ {a} ∪ B2)) = vbarSum w p (Finset.univ \ s) - vbarSum w p {a} - vbarSum w p B2 := by
              rw [ ← vbarSum_sdiff, ← vbarSum_sdiff ];
              · congr 1 ; ext ; simp +decide [ Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton ] ; tauto;
              · grind;
              · exact Finset.singleton_subset_iff.mpr ha.1;
            unfold vbarSum at * ; norm_num at * ; linarith [ hsmall a ];
  · contrapose! hsmall;
    by_cases h : ∃ g, p g > 0;
    · exact h.imp fun g hg => by linarith [ hw g, hp g, show 0 ≤ vbar w p g from le_max_of_le_left ( hp g ) ] ;
    · simp_all +decide [ show p = fun _ => 0 from funext fun _ => le_antisymm ( le_of_not_gt fun hi => h ⟨ _, hi ⟩ ) ( hp _ ) ];
      exact absurd hP ( not_lt_of_ge ( mul_nonneg ( by norm_num ) ( mul_nonneg ( by norm_num ) ( MMS_nonneg ( by norm_num ) _ _ hw ( fun _ => by norm_num ) ) ) ) )
end FairSelling
