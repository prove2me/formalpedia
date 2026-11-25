-- Prove2me | solution 1 for DedekindSubgroups.meyer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:09:16.380317+00:00
-- url     : https://prove2.me/submissions/6e8d14c4-2d8a-451c-897a-0b5cb39ba160

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer
public import Theorems.Thm_DedekindSubgroups_meyer_int
public import Theorems.Thm_DedekindSubgroups_sum_sig_perm
public import Theorems.Thm_DedekindSubgroups_sum_range_cast_id
public import Theorems.Thm_DedekindSubgroups_dedekindSum_residue

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}
namespace DedekindSubgroups
theorem _root_.solution (hk : 0 < k) (hinv : h * h' % k = 1) :
    12 * (k : ℚ) * dedekindSum h k = ((k : ℚ) - 1) * ((k : ℚ) - 2) - 4 * inv h k := by
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hM := congrArg (fun z : ℤ => (z : ℚ)) (meyer_int h k hk)
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_sum, Int.cast_sub, Int.cast_ofNat,
    Int.cast_one] at hM
  have hsplit : ∑ r ∈ range k, (2 * (k : ℚ) - 1 - 3 * r) * (sig h k r : ℚ)
      = (2 * (k : ℚ) - 1) * ∑ r ∈ range k, (sig h k r : ℚ) - 3 * ∑ r ∈ range k, (r : ℚ) * sig h k r := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl ?_; intro r _; ring
  have hS : (∑ r ∈ range k, (sig h k r : ℚ)) = ∑ r ∈ range k, (r : ℚ) :=
    sum_sig_perm hk hinv (fun z => (z : ℚ))
  rw [hsplit, hS, sum_range_cast_id] at hM
  rw [dedekindSum_residue hk hinv]
  field_simp
  linear_combination (16 : ℚ) * hM
end DedekindSubgroups
