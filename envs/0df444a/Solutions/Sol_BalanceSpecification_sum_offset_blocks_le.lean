-- Prove2me | solution 1 for BalanceSpecification.sum_offset_blocks_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:37:41.1248+00:00
-- url     : https://prove2.me/submissions/6e24010e-d40f-4f8b-a6cb-b1623ca7cd48

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {H : ℕ → ℕ → ℝ}
namespace BalanceSpecification
theorem _root_.solution (hnonneg : ∀ s l, 0 ≤ H s l)
    {n k N : ℕ} (hn : 0 < n) (hkn : k * n ≤ N) :
    (∑ r ∈ Finset.range n, ∑ j ∈ Finset.range k, H (r + j * n) n) ≤
      ∑ i ∈ Finset.range N, H i n := by
  classical
  let s := (Finset.range n) ×ˢ (Finset.range k)
  let f : ℕ × ℕ → ℕ := fun z => z.1 + z.2 * n
  have hinj : Set.InjOn f (s : Set (ℕ × ℕ)) := by
    intro a ha b hb he
    obtain ⟨har, haj⟩ := Finset.mem_product.mp ha
    obtain ⟨hbr, hbj⟩ := Finset.mem_product.mp hb
    have har' := Finset.mem_range.mp har
    have hbr' := Finset.mem_range.mp hbr
    have hj : a.2 = b.2 := by
      have hd := congrArg (fun t : ℕ => t / n) he
      change (a.1 + a.2 * n) / n = (b.1 + b.2 * n) / n at hd
      simpa only [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt har',
        Nat.div_eq_of_lt hbr', zero_add] using hd
    have hr : a.1 = b.1 := by
      change a.1 + a.2 * n = b.1 + b.2 * n at he
      rw [hj] at he
      exact Nat.add_right_cancel he
    exact Prod.ext hr hj
  have hsubset : s.image f ⊆ Finset.range N := by
    intro i hi
    obtain ⟨⟨r, j⟩, hj, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hr, hj⟩ := Finset.mem_product.mp hj
    have hr' := Finset.mem_range.mp hr
    have hj' := Finset.mem_range.mp hj
    have hmul : (j + 1) * n ≤ k * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hj')
    have hbound : r + j * n < N := by
      rw [Nat.add_mul, one_mul] at hmul
      omega
    exact Finset.mem_range.mpr hbound
  calc
    (∑ r ∈ Finset.range n, ∑ j ∈ Finset.range k, H (r + j * n) n) =
        ∑ z ∈ s, H (f z) n := by
      exact (Finset.sum_product _ _ (fun z : ℕ × ℕ => H (z.1 + z.2 * n) n)).symm
    _ = ∑ i ∈ s.image f, H i n := (Finset.sum_image (f := fun i : ℕ => H i n) hinj).symm
    _ ≤ ∑ i ∈ Finset.range N, H i n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i _ _ => hnonneg i n)
end BalanceSpecification
