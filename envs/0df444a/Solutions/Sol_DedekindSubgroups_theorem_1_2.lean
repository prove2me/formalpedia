-- Prove2me | solution 1 for DedekindSubgroups.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:17:11.464795+00:00
-- url     : https://prove2.me/submissions/c490e32d-8051-41d4-8486-da62b82edc80

module
public import Definitions.Def_DedekindSubgroups
public import Definitions.Def_DedekindSubgroups_Solution
public import Theorems.Thm_DedekindSubgroups_two_mul_subgroupSum_prime


set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p)
    (H : Subgroup (ZMod p)ˣ) (hodd : Odd (Nat.card H)) (hn : 1 < Nat.card H) :
    ∃ y : ℤ, (y : ℚ) = 2 * subgroupSum H ∧
      y ≡ (Nat.card H : ℤ) * (((p : ℤ) - 1) / 2) [ZMOD 8] :=
  two_mul_subgroupSum_prime hp3 H hodd hn
end DedekindSubgroups
