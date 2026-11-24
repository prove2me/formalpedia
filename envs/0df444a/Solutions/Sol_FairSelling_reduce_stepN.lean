-- Prove2me | solution 1 for FairSelling.reduce_stepN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:12.73284+00:00
-- url     : https://prove2.me/submissions/c799ce6b-ea87-4e49-afd8-d6e41da9e836

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (n : ℕ) (hn : 0 < n) (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (r : ℝ)
    (A : Fin n → Finset G) (s : Finset G) (q : Fin n → ℝ)
    (hcfg : ConfigN n w p r A s q) (hcard : n ≤ s.card) :
    ∃ (A' : Fin n → Finset G) (s' : Finset G) (q' : Fin n → ℝ),
      ConfigN n w p r A' s' q' ∧ s'.card < s.card := by
  obtain ⟨g, hg⟩ : ∃ g ∈ s, ∀ h ∈ s, p g ≤ p h := by
    exact Finset.exists_min_image _ _ ( Finset.card_pos.mp ( lt_of_lt_of_le hn hcard ) );
  obtain ⟨i, hi⟩ : ∃ i : Fin n, p g ≤ q i := by
    have h_bound : (n : ℝ) * p g ≤ ∑ i, q i := by
      rw [ hcfg.2.2.2.2.1 ];
      exact le_trans ( by simpa using mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr hcard ) ( hp g ) ) ( Finset.sum_le_sum hg.2 );
    contrapose! h_bound;
    simpa using Finset.sum_lt_sum_of_nonempty ⟨ ⟨ 0, hn ⟩, Finset.mem_univ _ ⟩ fun i _ => h_bound i;
  refine' ⟨ Function.update A i ( A i ∪ { g } ), s.erase g, Function.update q i ( q i - p g ), _, _ ⟩ <;> simp_all +decide [ ConfigN ];
  · refine' ⟨ _, _, _, _, _ ⟩;
    · intro j k hjk; by_cases hj : j = i <;> by_cases hk : k = i <;> simp_all +decide [ Finset.disjoint_left ] ;
      · grind;
      · grind +qlia;
      · exact hcfg.1 _ _ hjk;
    · intro j; by_cases hj : j = i <;> simp_all +decide [ Finset.disjoint_left ] ;
    · grind +qlia;
    · intro j; by_cases hj : j = i <;> simp +decide [ *, Function.update_apply ] ;
    · refine' ⟨ _, _ ⟩;
      · simp +decide [ ← hcfg.2.2.2.2.1, Finset.sum_update_of_mem ];
      · intro j; by_cases hj : j = i <;> simp_all +decide [ Function.update_apply ] ;
        by_cases h : g ∈ A i <;> simp_all +decide [ vbarSum ];
        · exact absurd ( Finset.disjoint_left.mp ( hcfg.2.1 i ) hg.1 h ) ( by simp +decide );
        · linarith [ hcfg.2.2.2.2.2 i, show vbar w p g ≥ p g from le_max_left _ _ ];
  · exact ⟨ g, hg.1 ⟩
end FairSelling
