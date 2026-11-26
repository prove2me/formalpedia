-- Prove2me | solution 1 for BandParity.parSign_two_mul_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:05:30.160921+00:00
-- url     : https://prove2.me/submissions/f8fa69ac-9949-47be-b855-84bd10dcefcf

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
public import Theorems.Thm_BandParity_val_two_mul_of_lt

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution (hp2 : p ≠ 2) {x : ZMod p} (hx : 2 * x.val < p) :
    parSign (2 * x) = 1 := by
  rw [parSign, val_two_mul_of_lt hp2 hx, pow_mul]; norm_num
end BandParity
