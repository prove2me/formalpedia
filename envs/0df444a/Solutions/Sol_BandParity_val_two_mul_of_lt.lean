-- Prove2me | solution 1 for BandParity.val_two_mul_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:02:24.553674+00:00
-- url     : https://prove2.me/submissions/27e2f728-6ec6-46f4-b52b-ae74f55ff373

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
public import Theorems.Thm_BandParity_val_two

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution (hp2 : p ≠ 2) {x : ZMod p} (hx : 2 * x.val < p) :
    (2 * x).val = 2 * x.val := by
  rw [ZMod.val_mul, val_two hp2, Nat.mod_eq_of_lt hx]
end BandParity
