-- Prove2me | solution 1 for BandParity.bandSignPow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:56:15.992737+00:00
-- url     : https://prove2.me/submissions/7a23c5e8-b412-4ce0-aa2e-e85e68384ec8

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
omit hN3
namespace BandParity
theorem _root_.solution {e : ℕ} (he0 : e ≠ 0) (u : (ZMod N)ˣ) :
    bandSignPow e u = uSign u * uSign (u ^ e) := by
  unfold bandSignPow uSign
  set v := (u : ZMod N).val with hv
  have hval : ((u ^ e : (ZMod N)ˣ) : ZMod N).val = v ^ e % N := by
    rw [Units.val_pow_eq_pow_val, show (u : ZMod N) = ((v : ℕ) : ZMod N) by
      rw [hv, ZMod.natCast_zmod_val], ← Nat.cast_pow, ZMod.val_natCast]
  rw [hval]
  have h1 : (-1 : ℤ) ^ (v ^ e) = (-1) ^ v := by
    rcases Nat.even_or_odd v with h | h
    · rw [h.neg_one_pow, (Nat.even_pow.2 ⟨h, he0⟩).neg_one_pow]
    · rw [h.neg_one_pow, (h.pow).neg_one_pow]
  have h2 : (-1 : ℤ) ^ (v ^ e) = (-1) ^ (v ^ e / N) * (-1) ^ (v ^ e % N) := by
    conv_lhs => rw [← Nat.div_add_mod (v ^ e) N]
    rw [pow_add, pow_mul, hN.neg_one_pow]
  have hr : (-1 : ℤ) ^ (v ^ e % N) * (-1) ^ (v ^ e % N) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have E := h1.symm.trans h2
  linear_combination (-((-1 : ℤ) ^ (v ^ e % N))) * E + (-((-1 : ℤ) ^ (v ^ e / N))) * hr
end BandParity
