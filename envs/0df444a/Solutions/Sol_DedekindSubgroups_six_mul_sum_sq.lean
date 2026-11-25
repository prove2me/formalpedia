-- Prove2me | solution 1 for DedekindSubgroups.six_mul_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:08:49.726391+00:00
-- url     : https://prove2.me/submissions/ef59ab00-eec6-4c42-8998-ee062fed2a3b

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution (m : ℕ) :
    6 * ∑ r ∈ range m, (r : ℤ) ^ 2 = (m : ℤ) * (m - 1) * (2 * m - 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, mul_add, ih]; push_cast; ring
end DedekindSubgroups
