-- Prove2me | solution 1 for BandParity.p_mul_S
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:06.517841+00:00
-- url     : https://prove2.me/submissions/9bcaa911-f9a9-4745-98c7-f442b49fe877

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
public import Theorems.Thm_BandParity_p_dvd_cosetSum

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (hp5 : 5 < p) (z : GaussianInt) : (p : ℤ) * S χ z = cosetSum χ z :=
  Int.mul_ediv_cancel' (p_dvd_cosetSum hχ hp5 z)
end BandParity
