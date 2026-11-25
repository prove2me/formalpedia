-- Prove2me | solution 1 for DedekindSubgroups.sig_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:09:18.743161+00:00
-- url     : https://prove2.me/submissions/11092436-0fba-458f-a019-8c36019ec08b

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution (h k r : ℕ) :
    (sig h k r : ℤ) = h * r - k * ((h * r / k : ℕ) : ℤ) := by
  unfold sig
  have h1 := Nat.div_add_mod (h * r) k
  have h2 : ((k * (h * r / k) + h * r % k : ℕ) : ℤ) = ((h * r : ℕ) : ℤ) := by rw [h1]
  simp only [Nat.cast_add, Nat.cast_mul] at h2
  linear_combination h2
end DedekindSubgroups
