-- Prove2me | solution 1 for DedekindSubgroups.sq_root_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:06:42.229152+00:00
-- url     : https://prove2.me/submissions/7fdd04cc-e969-4662-9318-80fb3099a5f3

module
public import Definitions.Def_DedekindSubgroups_Parity
public import Definitions.Def_DedekindSubgroups_Main

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {k : ℕ} [NeZero k]
variable {G : Type*} [Group G]
namespace DedekindSubgroups
theorem _root_.solution (hodd : Odd (Nat.card G)) (g : G) :
    g ^ ((Nat.card G + 1) / 2) * g ^ ((Nat.card G + 1) / 2) = g := by
  obtain ⟨m, hm⟩ := hodd
  rw [← pow_add, show (Nat.card G + 1) / 2 + (Nat.card G + 1) / 2 = Nat.card G + 1 by omega,
    pow_succ, pow_card_eq_one', one_mul]
end DedekindSubgroups
