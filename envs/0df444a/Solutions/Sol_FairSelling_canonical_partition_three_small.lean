-- Prove2me | solution 1 for FairSelling.canonical_partition_three_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:47:09.046607+00:00
-- url     : https://prove2.me/submissions/9a4d2fc8-cf1a-4104-8c79-6e3582df44f8

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_CanonicalPartition
import Theorems.Thm_FairSelling_greedy_two_bags
import Theorems.Thm_FairSelling_MMS_nonneg
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_three_MMS_le_vbarSum_univ
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hsmall : ∀ g, vbar w p g < (1/2) * MMS 3 w p) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonical w p ((3/4) * MMS 3 w p) kept sold money leftover := by
  by_cases hMMS : MMS 3 w p = 0;
  · refine' ⟨ fun _ => ∅, ∅, fun _ => 0, 0, _, _, _, _, _ ⟩ <;> simp +decide [ hMMS ];
    exact Finset.sum_nonneg fun _ _ => le_max_of_le_left ( hp _ );
  · obtain ⟨B1, B2, hB1, hB2, hdisj, hsum1, hsum2, hsum3⟩ : ∃ B1 B2 : Finset G, B1 ⊆ Finset.univ ∧ B2 ⊆ Finset.univ ∧ Disjoint B1 B2 ∧ 3 / 4 * MMS 3 w p ≤ ∑ g ∈ B1, vbar w p g ∧ 3 / 4 * MMS 3 w p ≤ ∑ g ∈ B2, vbar w p g ∧ (∑ g ∈ B1, vbar w p g) + (∑ g ∈ B2, vbar w p g) ≤ 3 * (3 / 4 * MMS 3 w p) := by
      apply greedy_two_bags (fun g => vbar w p g) (fun g => by
        exact le_max_of_le_left ( hp g )) (3 / 4 * MMS 3 w p) (by
      exact mul_pos ( by norm_num ) ( lt_of_le_of_ne ( MMS_nonneg ( by norm_num ) w p hw hp ) ( Ne.symm hMMS ) )) Finset.univ (by
      exact fun g _ => by linarith [ hsmall g ] ;) (by
      have := three_MMS_le_vbarSum_univ w p hw hp;
      linarith! [ show 0 ≤ MMS 3 w p from MMS_nonneg ( by decide ) w p hw hp ]);
    refine' ⟨ fun k => if k = 0 then B1 else if k = 1 then B2 else Finset.univ \ ( B1 ∪ B2 ), ∅, fun _ => 0, 2, _, _, _, _, _ ⟩ <;> simp +decide;
    · simp +decide [ Fin.forall_fin_succ, Finset.disjoint_left ];
      simp_all +decide [ Finset.disjoint_left ];
      exact fun g hg1 hg2 => hdisj hg2 hg1;
    · intro k
      fin_cases k <;> simp +decide [ * ];
      · exact hsum1;
      · exact hsum2;
      · have hsum_univ : vbarSum w p Finset.univ = ∑ g ∈ B1, vbar w p g + ∑ g ∈ B2, vbar w p g + vbarSum w p (Finset.univ \ (B1 ∪ B2)) := by
          unfold vbarSum; simp +decide [ * ] ;
          rw [ Finset.sum_union hdisj ] ; ring;
        linarith [ three_MMS_le_vbarSum_univ w p hw hp ]
end FairSelling
