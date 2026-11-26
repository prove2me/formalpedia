-- Prove2me | solution 1 for BandParity.bandSum_re_modEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:15:54.749917+00:00
-- url     : https://prove2.me/submissions/4016793d-e860-4bf8-ab80-e5a6d5f2868b

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
public import Theorems.Thm_P2M_BandParity_bandSum_re_modEq__b570c65110c7


set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (hp8 : p % 8 = 5) :
    (bandSum χ).re ≡ Q p [ZMOD 4] :=
  bandSum_re_modEq' hχ hp8
end BandParity
