-- Prove2me | solution 1 for BandParity.sign_mul_modEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:56:00.138102+00:00
-- url     : https://prove2.me/submissions/31af7ab7-b350-42ff-b432-9e3e5b9cbcd3

module
public import Mathlib
public import Definitions.Def_BandParity_Matching

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
namespace BandParity
theorem _root_.solution {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b ≡ a + b - 1 [ZMOD 4] := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
end BandParity
