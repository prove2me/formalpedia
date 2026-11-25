-- Prove2me | solution 1 for DedekindSubgroups.inv_one_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:06:34.435825+00:00
-- url     : https://prove2.me/submissions/39de359f-658f-4748-9598-023725219b07

module
public import Definitions.Def_DedekindSubgroups_Parity
public import Definitions.Def_DedekindSubgroups_Main

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {k : ℕ} [NeZero k]
namespace DedekindSubgroups
theorem _root_.solution (k : ℕ) : inv 1 k = 0 := by
  unfold inv
  refine sum_eq_zero ?_
  intro y hy
  refine sum_eq_zero ?_
  intro x hx
  rw [mem_range] at hx hy
  simp only [sig, one_mul, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt (lt_trans hx hy)]
  rw [ite_eq_right_iff]
  intro hlt
  omega
end DedekindSubgroups
