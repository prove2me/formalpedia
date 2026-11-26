-- Prove2me | solution 1 for BandParity.val_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:01:15.886785+00:00
-- url     : https://prove2.me/submissions/0ae74aac-e3e4-49a9-b4d0-79e7358a1aff

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution (hp2 : p ≠ 2) : (2 : ZMod p).val = 2 := by
  have : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)
  rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast, ZMod.val_natCast,
    Nat.mod_eq_of_lt this]
end BandParity
