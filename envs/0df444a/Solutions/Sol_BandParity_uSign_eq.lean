-- Prove2me | solution 1 for BandParity.uSign_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:56:04.563838+00:00
-- url     : https://prove2.me/submissions/0144ae98-b16f-4c80-858f-016178e91914

module
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_OddSubgroup

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {N : ℕ} [NeZero N]
omit [NeZero N]
namespace BandParity
theorem _root_.solution (u : (ZMod N)ˣ) : uSign u = 1 ∨ uSign u = -1 := neg_one_pow_eq_or ℤ _
end BandParity
