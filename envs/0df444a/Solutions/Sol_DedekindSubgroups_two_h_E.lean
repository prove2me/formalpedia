-- Prove2me | solution 1 for DedekindSubgroups.two_h_E
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:12:58.562964+00:00
-- url     : https://prove2.me/submissions/6ba04f23-5eef-4d40-81d3-fdc9c31f0ecf

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
public import Theorems.Thm_DedekindSubgroups_sig_eq_sub
public import Theorems.Thm_DedekindSubgroups_E_eq
public import Theorems.Thm_DedekindSubgroups_sum_sig_perm


set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}
namespace DedekindSubgroups
theorem _root_.solution (hk : 0 < k) (hinv : h * h' % k = 1) :
    2 * (h : ℤ) * E h k = ((h : ℤ) ^ 2 + 1) * ∑ r ∈ range k, (r : ℤ) ^ 2
      - (k : ℤ) ^ 2 * ∑ r ∈ range k, ((h * r / k : ℕ) : ℤ) ^ 2 := by
  have hsq : ∑ r ∈ range k, (sig h k r : ℤ) ^ 2 = ∑ r ∈ range k, (r : ℤ) ^ 2 :=
    sum_sig_perm hk hinv (fun z => (z : ℤ) ^ 2)
  have hQ : ∑ r ∈ range k, (sig h k r : ℤ) ^ 2
      = (h : ℤ) ^ 2 * ∑ r ∈ range k, (r : ℤ) ^ 2
        - 2 * h * k * ∑ r ∈ range k, (r : ℤ) * ((h * r / k : ℕ) : ℤ)
        + (k : ℤ) ^ 2 * ∑ r ∈ range k, ((h * r / k : ℕ) : ℤ) ^ 2 := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl (fun r _ => ?_)
    rw [sig_eq_sub]; ring
  rw [E_eq]
  linear_combination hsq - hQ
end DedekindSubgroups
