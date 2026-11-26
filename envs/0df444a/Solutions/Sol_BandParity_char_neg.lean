-- Prove2me | solution 1 for BandParity.char_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:01:05.405401+00:00
-- url     : https://prove2.me/submissions/14c8ace6-2845-4c91-b91b-6ffc7cb35c25

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
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
omit hχ
namespace BandParity
theorem _root_.solution (hodd : χ (-1) = -1) (x : ZMod p) : χ (-x) = -χ x := by
  rw [show -x = -1 * x by ring, map_mul, hodd, neg_one_mul]
end BandParity
