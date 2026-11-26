-- Prove2me | solution 1 for BandParity.bandSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:54.023274+00:00
-- url     : https://prove2.me/submissions/0646ac8e-10d2-41b8-855d-22a80b852a10

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
public import Theorems.Thm_BandParity_parSign_neg
public import Theorems.Thm_P2M_BandParity_neg_one_pow_band__5cb4cffc3c5e
public import Theorems.Thm_BandParity_sum_eq_two_nsmul_half
public import Theorems.Thm_BandParity_char_neg
public import Theorems.Thm_BandParity_sum_char_mul_odd
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_quartic_apply_neg_one
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (hp8 : p % 8 = 5) :
    bandSum χ = ((∑ u ∈ cls χ 1, parSign u * parSign (u ^ 2) : ℤ) : GaussianInt)
      + gi * ((∑ u ∈ cls χ gi, parSign u * parSign (u ^ 2) : ℤ) : GaussianInt) := by
  have hp2 : p ≠ 2 := by omega
  have hodd := quartic_apply_neg_one χ hχ hp8
  set w : ZMod p → ℤ := fun x => parSign x * parSign (x ^ 2) with hw
  have hwodd : ∀ x ≠ 0, w (-x) = -w x := by
    intro x hx; simp only [hw, neg_sq, parSign_neg hp2 hx, neg_mul]
  have hfull := sum_char_mul_odd hχ hodd w hwodd
  have hhalf := sum_eq_two_nsmul_half hp2 (fun x => χ x * (w x : GaussianInt))
    (by simp [MulChar.map_zero]) (fun x => by
      by_cases hx : x = 0
      · subst hx; simp
      · simp only [hwodd x hx, char_neg hodd]; push_cast; ring)
  have hB : bandSum χ = ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p),
      χ x * (w x : GaussianInt) := by
    unfold bandSum
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hw]; simp only
    rw [← neg_one_pow_band' hp2 x]; push_cast; rfl
  rw [← hB, two_nsmul, ← two_mul, hfull] at hhalf
  exact (mul_left_cancel₀ two_ne_zero hhalf).symm
end BandParity
