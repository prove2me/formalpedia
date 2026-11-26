-- Prove2me | solution 1 for BandParity.uSign_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:56:15.508959+00:00
-- url     : https://prove2.me/submissions/525d1140-76be-4d31-96ed-b2eb84f9cc97

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
namespace BandParity
theorem _root_.solution (u : (ZMod N)ˣ) : uSign (-u) = -uSign u := by
  have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 (by omega)
  unfold uSign
  rw [Units.val_neg, ZMod.neg_val]; simp only [u.ne_zero, ↓reduceIte]
  have hv := ZMod.val_lt (u : ZMod N)
  have h : (-1 : ℤ) ^ (N - (u : ZMod N).val) * (-1) ^ (u : ZMod N).val = -1 := by
    rw [← pow_add, Nat.sub_add_cancel hv.le, hN.neg_one_pow]
  rcases neg_one_pow_eq_or ℤ (u : ZMod N).val with h' | h' <;> rw [h'] at h ⊢ <;> linarith
end BandParity
