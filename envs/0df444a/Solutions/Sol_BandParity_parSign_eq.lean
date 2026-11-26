-- Prove2me | solution 1 for BandParity.parSign_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:01:59.547007+00:00
-- url     : https://prove2.me/submissions/822f653e-621b-413f-8f39-641dbbc9633c

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
omit hp
namespace BandParity
theorem _root_.solution (x : ZMod p) : parSign x = 1 ∨ parSign x = -1 :=
  neg_one_pow_eq_or ℤ _
end BandParity
