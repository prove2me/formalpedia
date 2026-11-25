-- Prove2me | solution 1 for DedekindSubgroups.sum_range_cast_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:04:25.068064+00:00
-- url     : https://prove2.me/submissions/1bcdf6a3-bf07-489c-808e-bb14bb2f0957

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}
namespace DedekindSubgroups
theorem _root_.solution (k : ℕ) : (∑ r ∈ range k, (r : ℚ)) = (k : ℚ) * (k - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring
end DedekindSubgroups
