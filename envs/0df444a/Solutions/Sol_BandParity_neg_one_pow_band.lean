-- Prove2me | solution 1 for BandParity.neg_one_pow_band
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:14:42.348007+00:00
-- url     : https://prove2.me/submissions/944b35fe-e875-4549-8615-86abf8ffbfd0

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
public import Theorems.Thm_P2M_BandParity_neg_one_pow_band__5cb4cffc3c5e


set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution (hp2 : p ≠ 2) (x : ZMod p) :
    (-1 : ℤ) ^ band x = parSign x * parSign (x ^ 2) :=
  neg_one_pow_band' hp2 x
end BandParity
