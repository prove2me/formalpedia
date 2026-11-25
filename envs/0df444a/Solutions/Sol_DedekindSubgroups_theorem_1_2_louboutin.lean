-- Prove2me | solution 1 for DedekindSubgroups.theorem_1_2_louboutin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:19:33.466494+00:00
-- url     : https://prove2.me/submissions/9fea9ec3-4fab-4fc7-82f0-b858720ab6e4

module
public import Definitions.Def_DedekindSubgroups
public import Definitions.Def_DedekindSubgroups_Solution
public import Theorems.Thm_DedekindSubgroups_louboutin_N_modEq


set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p)
    (H : Subgroup (ZMod p)ˣ) (hodd : Odd (Nat.card H)) (hn : 1 < Nat.card H) :
    ∃ N : ℤ, (N : ℚ) = 12 * subgroupSum H - p ∧
      N ≡ 3 * (Nat.card H : ℤ) * ((p : ℤ) - 1) - p [ZMOD 48] :=
  louboutin_N_modEq hp3 H hodd hn
end DedekindSubgroups
