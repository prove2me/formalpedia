-- Prove2me | solution 1 for BandParity.bandSum_im_modEq_coords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:16:42.949988+00:00
-- url     : https://prove2.me/submissions/af53b74d-4132-44c0-a7fc-0fc8f9acf289

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
public import Theorems.Thm_P2M_BandParity_bandSum_im_modEq_coords__b7058f26c914


set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    (bandSum χ).im ≡ Q p + k χ + t χ [ZMOD 4] :=
  bandSum_im_modEq_coords' hχ hp8 hp5 hpin
end BandParity
