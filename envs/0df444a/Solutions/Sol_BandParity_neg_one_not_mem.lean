-- Prove2me | solution 1 for BandParity.neg_one_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:56:24.48575+00:00
-- url     : https://prove2.me/submissions/b693bc6a-c41f-4920-b59f-65a6e574cf22

module
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_OddSubgroup

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {N : ℕ} [NeZero N]
variable (hN : Odd N) (hN3 : 3 ≤ N)
include hN hN3
variable {H : Subgroup (ZMod N)ˣ} [DecidablePred (· ∈ H)] (hH : Odd (Nat.card H))
include hH
omit [NeZero N] hN [DecidablePred (· ∈ H)]
namespace BandParity
theorem _root_.solution : (-1 : (ZMod N)ˣ) ∉ H := by
  intro hm
  have : Fact (2 < N) := ⟨by omega⟩
  have hne : (-1 : (ZMod N)ˣ) ≠ 1 := by
    intro h
    exact ZMod.neg_one_ne_one (congrArg Units.val h)
  have hord : orderOf (-1 : (ZMod N)ˣ) = 2 :=
    orderOf_eq_prime (by rw [neg_one_sq]) hne
  have := Subgroup.orderOf_dvd_natCard H hm
  rw [hord] at this
  exact (Nat.not_even_iff_odd.2 hH) (even_iff_two_dvd.2 this)
end BandParity
