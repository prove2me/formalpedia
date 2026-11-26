-- Prove2me | solution 1 for BandParity.quadraticChar_of_char_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:18.011113+00:00
-- url     : https://prove2.me/submissions/a1529c2d-792e-4cd5-9987-abe0017b1521

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
theorem _root_.solution {x : ZMod p} (hx : x ≠ 0) (h : χ x = 1 ∨ χ x = -1) :
    quadraticChar (ZMod p) x = 1 :=
  (quadraticChar_one_iff_isSquare hx).2 ((isSquare_iff_char hχ hx).2 h)
end BandParity
