-- Prove2me | solution 1 for BandParity.odd_k
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:14:58.396106+00:00
-- url     : https://prove2.me/submissions/21efe965-8428-45da-b0dc-402c7ad4f75c

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
public import Theorems.Thm_P2M_BandParity_odd_k__12c0ba03e16b


set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (hp8 : p % 8 = 5) (hp5 : 5 < p) : Odd (k χ) :=
  odd_k' hχ hp8 hp5
end BandParity
