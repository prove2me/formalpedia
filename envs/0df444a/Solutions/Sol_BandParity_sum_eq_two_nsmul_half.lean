-- Prove2me | solution 1 for BandParity.sum_eq_two_nsmul_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:02:35.281243+00:00
-- url     : https://prove2.me/submissions/bbf7f608-9b9e-40cf-b627-f66716734434

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_val_neg_of_ne_zero
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution {R : Type*} [AddCommMonoid R] (hp2 : p ≠ 2) (h : ZMod p → R)
    (h0 : h 0 = 0) (hsym : ∀ x, h (-x) = h x) :
    ∑ x, h x = 2 • ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p), h x := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun x : ZMod p => 2 * x.val < p), two_nsmul]
  congr 1
  simp only [Finset.sum_filter]
  refine (Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun x => ?_).symm
  simp only [Equiv.neg_apply]
  by_cases hx : x = 0
  · subst hx; simp [h0, hp.out.pos]
  · rw [val_neg_of_ne_zero hx, hsym]
    have hv := ZMod.val_lt x
    have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
    by_cases hc : 2 * x.val < p
    · have : ¬ 2 * (p - x.val) < p := by omega
      simp [hc, this]
    · have : 2 * (p - x.val) < p := by omega
      simp [hc, this]
end BandParity
