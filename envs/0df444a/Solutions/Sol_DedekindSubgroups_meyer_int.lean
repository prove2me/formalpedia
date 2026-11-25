-- Prove2me | solution 1 for DedekindSubgroups.meyer_int
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:06:20.276018+00:00
-- url     : https://prove2.me/submissions/cce23091-3da8-42b8-9280-334da14d19e6

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer
public import Theorems.Thm_DedekindSubgroups_sig_sub
public import Theorems.Thm_DedekindSubgroups_sum_pairs_diff
public import Theorems.Thm_DedekindSubgroups_sum_pairs_left
public import Theorems.Thm_DedekindSubgroups_sum_pairs_right


set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution (h k : ℕ) (hk : 0 < k) :
    (k : ℤ) * inv h k = ∑ r ∈ range k, (2 * (k : ℤ) - 1 - 3 * r) * sig h k r := by
  -- sum the pointwise identity over all pairs x < y < k
  have hpair : ∀ y ∈ range k, ∀ x ∈ range y,
      (k : ℤ) * (if sig h k y < sig h k x then 1 else 0)
        = (sig h k (y - x) : ℤ) - ((sig h k y : ℤ) - sig h k x) := by
    intro y _ x hx
    have := sig_sub h k x y hk (le_of_lt (mem_range.mp hx))
    linarith
  have h0 : sig h k 0 = 0 := by simp [sig]
  calc (k : ℤ) * inv h k
      = ∑ y ∈ range k, ∑ x ∈ range y, (k : ℤ) * (if sig h k y < sig h k x then 1 else 0) := by
        unfold inv; push_cast; rw [mul_sum]; refine sum_congr rfl ?_; intro y _; rw [mul_sum]
    _ = ∑ y ∈ range k, ∑ x ∈ range y,
          ((sig h k (y - x) : ℤ) - ((sig h k y : ℤ) - sig h k x)) := by
        refine sum_congr rfl ?_; intro y hy; refine sum_congr rfl ?_; intro x hx
        exact hpair y hy x hx
    _ = ∑ y ∈ range k, ∑ x ∈ range y, (sig h k (y - x) : ℤ)
          - ∑ y ∈ range k, ∑ _x ∈ range y, (sig h k y : ℤ)
          + ∑ y ∈ range k, ∑ x ∈ range y, (sig h k x : ℤ) := by
        simp only [← sum_sub_distrib, ← sum_add_distrib]
        refine sum_congr rfl ?_; intro y _; refine sum_congr rfl ?_; intro x _; ring
    _ = ∑ u ∈ range k, ((k : ℤ) - u) * sig h k u
          - ∑ y ∈ range k, (y : ℤ) * sig h k y
          + ∑ x ∈ range k, ((k : ℤ) - 1 - x) * sig h k x := by
        rw [sum_pairs_diff (fun z => (sig h k z : ℤ)) (by simp [h0]) k,
          sum_pairs_right (fun z => (sig h k z : ℤ)) k, sum_pairs_left (fun z => (sig h k z : ℤ)) k]
    _ = ∑ r ∈ range k, (2 * (k : ℤ) - 1 - 3 * r) * sig h k r := by
        simp only [← sum_sub_distrib, ← sum_add_distrib]
        refine sum_congr rfl ?_; intro r _; ring
end DedekindSubgroups
