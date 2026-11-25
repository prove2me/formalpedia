-- Prove2me | solution 1 for DedekindSubgroups.eq_one_of_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:06:58.394182+00:00
-- url     : https://prove2.me/submissions/1bfd8f0b-9ca4-48e0-8431-f61b0be15af5

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
theorem _root_.solution (hodd : Odd (Nat.card G)) {g : G} (hg : g⁻¹ = g) : g = 1 := by
  obtain ⟨m, hm⟩ := hodd
  have h2 : g ^ 2 = 1 := by rw [sq]; nth_rewrite 1 [← hg]; exact inv_mul_cancel g
  have hn : g ^ Nat.card G = 1 := pow_card_eq_one'
  rw [hm, pow_succ, pow_mul, h2, one_pow, one_mul] at hn
  exact hn
end DedekindSubgroups
