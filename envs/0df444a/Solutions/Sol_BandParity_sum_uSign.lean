-- Prove2me | solution 1 for BandParity.sum_uSign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:57:14.026417+00:00
-- url     : https://prove2.me/submissions/d971cb8a-3fb3-41c1-aa97-f11217decc64

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
omit [NeZero N] hN hN3 hH
namespace BandParity
theorem _root_.solution (S : Finset (ZMod N)ˣ) :
    ∑ u ∈ S, uSign u = (S.card : ℤ) - 2 * oddCount S := by
  unfold oddCount
  have : ∀ u : (ZMod N)ˣ, uSign u = 1 - 2 * (if Odd (u : ZMod N).val then 1 else 0) := by
    intro u
    unfold uSign
    rcases Nat.even_or_odd (u : ZMod N).val with h | h
    · rw [h.neg_one_pow]; split_ifs with hh
      · exact absurd hh (Nat.not_odd_iff_even.2 h)
      · ring
    · rw [h.neg_one_pow]; split_ifs; ring
  rw [Finset.sum_congr rfl (fun u _ => this u), Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_boole]
  simp
end BandParity
