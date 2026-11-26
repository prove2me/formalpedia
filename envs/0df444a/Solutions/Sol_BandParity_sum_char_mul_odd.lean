-- Prove2me | solution 1 for BandParity.sum_char_mul_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:49.800477+00:00
-- url     : https://prove2.me/submissions/0085eef1-e603-4e98-a880-e05aa8ed6fc9

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
public import Theorems.Thm_BandParity_gi_ne_zero
public import Theorems.Thm_BandParity_sum_char_mul
public import Theorems.Thm_BandParity_sum_cls_neg

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (hodd : χ (-1) = -1) (g : ZMod p → ℤ) (hg : ∀ x ≠ 0, g (-x) = -g x) :
    ∑ x, χ x * (g x : GaussianInt) =
      2 * (((∑ x ∈ cls χ 1, g x : ℤ) : GaussianInt)
        + gi * ((∑ x ∈ cls χ gi, g x : ℤ) : GaussianInt)) := by
  rw [sum_char_mul hχ, sum_cls_neg hodd g hg one_ne_zero, sum_cls_neg hodd g hg gi_ne_zero]
  push_cast; ring
end BandParity
