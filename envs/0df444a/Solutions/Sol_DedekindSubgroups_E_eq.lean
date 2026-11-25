-- Prove2me | solution 1 for DedekindSubgroups.E_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:10:53.594865+00:00
-- url     : https://prove2.me/submissions/9b46bf65-a0fa-4db0-911f-ea57a779c794

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
public import Theorems.Thm_DedekindSubgroups_sig_eq_sub

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution (h k : ℕ) :
    E h k = h * ∑ r ∈ range k, (r : ℤ) ^ 2 - k * ∑ r ∈ range k, (r : ℤ) * ((h * r / k : ℕ) : ℤ) := by
  unfold E
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl (fun r _ => ?_)
  rw [sig_eq_sub]; ring
end DedekindSubgroups
