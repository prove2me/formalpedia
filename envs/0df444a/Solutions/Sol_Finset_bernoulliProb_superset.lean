-- Prove2me | solution 1 for Finset.bernoulliProb_superset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:00:20.981424+00:00
-- url     : https://prove2.me/submissions/bde8c06b-4ab3-4239-aeed-bca498656779

module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Theorems.Thm_Finset_sum_bernoulliWeight

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Finset
variable {α : Type*} [DecidableEq α] (U : Finset α) (p : ℝ)
variable {U p}
namespace Finset
theorem _root_.solution {F : Finset α} (hF : F ⊆ U) :
    U.bernoulliProb p (F ⊆ ·) = p ^ #F := by
  unfold bernoulliProb
  have key : ∀ A ∈ U.powerset.filter (F ⊆ ·),
      U.bernoulliWeight p A = p ^ #F * (U \ F).bernoulliWeight p (A \ F) := by
    intro A hA
    obtain ⟨hAU, hFA⟩ := mem_filter.mp hA
    rw [mem_powerset] at hAU
    rw [bernoulliWeight, bernoulliWeight, sdiff_sdiff_sdiff_cancel_right hFA,
      card_sdiff_of_subset hFA, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' (card_le_card hFA)]
  rw [sum_congr rfl key, ← mul_sum]
  conv_rhs => rw [← mul_one (p ^ #F), ← sum_bernoulliWeight (U \ F) p]
  congr 1
  refine sum_nbij' (· \ F) (· ∪ F) (fun A hA => ?_) (fun B hB => ?_) (fun A hA => ?_)
    (fun B hB => ?_) fun _ _ => rfl
  · obtain ⟨hAU, -⟩ := mem_filter.mp hA
    exact mem_powerset.mpr (sdiff_subset_sdiff (mem_powerset.mp hAU) (Subset.refl F))
  · rw [mem_powerset] at hB
    refine mem_filter.mpr ⟨mem_powerset.mpr (union_subset (hB.trans sdiff_subset) hF),
      subset_union_right⟩
  · exact sdiff_union_of_subset (mem_filter.mp hA).2
  · rw [mem_powerset] at hB
    exact union_sdiff_cancel_right (disjoint_of_subset_left hB disjoint_sdiff_self_left)
end Finset
