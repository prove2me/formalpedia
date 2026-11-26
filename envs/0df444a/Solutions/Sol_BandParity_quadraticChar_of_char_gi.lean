-- Prove2me | solution 1 for BandParity.quadraticChar_of_char_gi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:09.37459+00:00
-- url     : https://prove2.me/submissions/bae6154f-67d7-4484-a0ec-1ca7864a1de4

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_isSquare_iff_char

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution {x : ZMod p} (hx : x ≠ 0) (h : χ x = gi ∨ χ x = -gi) :
    quadraticChar (ZMod p) x = -1 := by
  rw [quadraticChar_neg_one_iff_not_isSquare, isSquare_iff_char hχ hx]
  rintro (h' | h') <;> rcases h with h | h <;> rw [h] at h' <;> revert h' <;> decide
end BandParity
