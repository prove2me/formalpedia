-- Prove2me | solution 1 for BandParity.odd_t
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:15:04.953133+00:00
-- url     : https://prove2.me/submissions/5dc04924-0b77-47f9-81e9-e4c7d84880aa

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
public import Theorems.Thm_P2M_BandParity_odd_t__8898b1b7a17c


set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (hp8 : p % 8 = 5) (hp5 : 5 < p) : Odd (t χ) :=
  odd_t' hχ hp8 hp5
end BandParity
