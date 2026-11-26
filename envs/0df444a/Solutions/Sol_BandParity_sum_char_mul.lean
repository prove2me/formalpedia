-- Prove2me | solution 1 for BandParity.sum_char_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:33.9398+00:00
-- url     : https://prove2.me/submissions/6d66ea0b-8d93-4909-af75-cb833207c240

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
public import Theorems.Thm_BandParity_gi_ne_zero
public import Theorems.Thm_BandParity_zero_ne_gi
public import Theorems.Thm_BandParity_distinct
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_quartic_values
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
theorem _root_.solution (g : ZMod p → ℤ) :
    ∑ x, χ x * (g x : GaussianInt) =
      ((∑ x ∈ cls χ 1, g x : ℤ) : GaussianInt) + gi * ((∑ x ∈ cls χ gi, g x : ℤ) : GaussianInt)
        - ((∑ x ∈ cls χ (-1), g x : ℤ) : GaussianInt)
        - gi * ((∑ x ∈ cls χ (-gi), g x : ℤ) : GaussianInt) := by
  simp only [cls, Finset.sum_filter, Int.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x = 0
  · subst hx; simp [MulChar.map_zero, zero_ne_gi, gi_ne_zero]
  · rcases quartic_values χ hχ hx with h | h | h | h <;> rw [h] <;> simp [distinct]
end BandParity
