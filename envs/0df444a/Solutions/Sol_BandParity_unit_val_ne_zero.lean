-- Prove2me | solution 1 for BandParity.unit_val_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:56:14.241258+00:00
-- url     : https://prove2.me/submissions/779457c8-fa17-42f2-b30a-559bce452675

module
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_OddSubgroup

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {N : ℕ} [NeZero N]
variable (hN : Odd N) (hN3 : 3 ≤ N)
include hN hN3
omit [NeZero N] hN
namespace BandParity
theorem _root_.solution (u : (ZMod N)ˣ) : (u : ZMod N).val ≠ 0 := by
  have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 (by omega)
  intro h; exact u.ne_zero ((ZMod.val_eq_zero _).1 h)
end BandParity
