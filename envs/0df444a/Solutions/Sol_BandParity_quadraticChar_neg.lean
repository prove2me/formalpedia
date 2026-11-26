-- Prove2me | solution 1 for BandParity.quadraticChar_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:51.724074+00:00
-- url     : https://prove2.me/submissions/f7fb4a71-dd7a-4e1b-8496-08a9d753b5b6

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_ringChar_ne_two

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution (hp4 : p % 4 = 1) (x : ZMod p) :
    quadraticChar (ZMod p) (-x) = quadraticChar (ZMod p) x := by
  have hp2 : p ≠ 2 := by omega
  rw [show -x = -1 * x by ring, map_mul, quadraticChar_neg_one (ringChar_ne_two hp2), ZMod.card,
    ZMod.χ₄_nat_one_mod_four hp4, one_mul]
end BandParity
