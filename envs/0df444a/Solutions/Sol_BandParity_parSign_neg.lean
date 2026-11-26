-- Prove2me | solution 1 for BandParity.parSign_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:02:14.173524+00:00
-- url     : https://prove2.me/submissions/3927ce95-d12e-4f14-a7c9-54c1d134b89d

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
public import Theorems.Thm_BandParity_val_neg_of_ne_zero


set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) : parSign (-x) = -parSign x := by
  unfold parSign
  rw [val_neg_of_ne_zero hx]
  have hv := ZMod.val_lt x
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  have h : (-1 : ℤ) ^ (p - x.val) * (-1) ^ x.val = -1 := by
    rw [← pow_add, Nat.sub_add_cancel hv.le, hpodd.neg_one_pow]
  rcases neg_one_pow_eq_or ℤ x.val with h' | h' <;> rw [h'] at h ⊢ <;> linarith
end BandParity
