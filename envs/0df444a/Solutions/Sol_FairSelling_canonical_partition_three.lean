-- Prove2me | solution 1 for FairSelling.canonical_partition_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:47:12.248013+00:00
-- url     : https://prove2.me/submissions/a3e4d31b-bdc2-4d3f-a084-163c59ae8eeb

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_CanonicalPartition
import Theorems.Thm_FairSelling_canonical_items_money
import Theorems.Thm_FairSelling_exists_reduced_three
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hsmall : ∀ g, vbar w p g < (3/4) * MMS 3 w p) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonical w p ((3/4) * MMS 3 w p) kept sold money leftover := by
  obtain ⟨A, s, q, hcfg, hscard⟩ := exists_reduced_three w p hw hp;
  obtain ⟨hdisjA, hdisjs, hcover, hq0, hqsum, hge⟩ := hcfg;
  -- Let's establish the value identity `hVeq : vbarSum w p (Finset.univ \ s) + ∑ g ∈ s, p g = ∑ i : Fin 3, (vbarSum w p (A i) + q i)`.
  have hVeq : vbarSum w p (Finset.univ \ s) + ∑ g ∈ s, p g = ∑ i, (vbarSum w p (A i) + q i) := by
    have hVeq : vbarSum w p (Finset.univ \ s) = ∑ i : Fin 3, vbarSum w p (A i) := by
      rw [ show Finset.univ \ s = Finset.biUnion Finset.univ A from ?_ ];
      · rw [ vbarSum, Finset.sum_biUnion ];
        · rfl;
        · exact fun i _ j _ hij => hdisjA i j hij;
      · simp_all +decide [ Finset.ext_iff ];
        exact fun g => ⟨ fun hg => by simpa [ hg ] using hcover g, fun ⟨ i, hi ⟩ => fun hg => Finset.disjoint_left.mp ( hdisjs i ) hg hi ⟩;
    simp +decide [ *, Finset.sum_add_distrib ];
  by_cases hbig : ∃ i j : Fin 3, i ≠ j ∧ (1 / 4) * MMS 3 w p < q i ∧ (1 / 4) * MMS 3 w p < q j;
  · obtain ⟨ i, j, hij, hi, hj ⟩ := hbig;
    apply canonical_items_money w p hw hp hsmall s hscard;
    · rw [ ← hqsum, Fin.sum_univ_three ];
      fin_cases i <;> fin_cases j <;> simp +decide at hij hi hj ⊢ <;> linarith! [ hq0 0, hq0 1, hq0 2 ];
    · linarith [ hge i, hge j, show ∑ i, ( vbarSum w p ( A i ) + q i ) ≥ 3 * MMS 3 w p by exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun i _ => hge i ) ];
  · -- Define `leftover` as the index with the largest money.
    obtain ⟨leftover, hleftover⟩ : ∃ leftover : Fin 3, ∀ i, i ≠ leftover → q i ≤ (1 / 4) * MMS 3 w p := by
      contrapose! hbig;
      obtain ⟨ i, hi, hi' ⟩ := hbig 0; obtain ⟨ j, hj, hj' ⟩ := hbig i; use i, j; aesop;
    refine' ⟨ A, s, fun i => if i = leftover then q i else 0, leftover, _, _, _, _, _ ⟩ <;> simp_all +decide [ Fin.sum_univ_three ];
    · exact fun k => by split_ifs <;> linarith [ hq0 leftover ] ;
    · fin_cases leftover <;> linarith! [ hq0 0, hq0 1, hq0 2 ];
    · grind
end FairSelling
