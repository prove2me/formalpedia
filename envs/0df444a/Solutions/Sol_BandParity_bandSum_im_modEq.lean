-- Prove2me | solution 1 for BandParity.bandSum_im_modEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:17:06.476094+00:00
-- url     : https://prove2.me/submissions/904ea2e9-d5ef-4b76-ae36-b595de72e089

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
public import Theorems.Thm_P2M_BandParity_bandSum_im_modEq__c2ed66fd08bb


set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (hp8 : p % 8 = 5) (hpin : χ 2 = gi) :
    (bandSum χ).im ≡ kappa p [ZMOD 4] :=
  bandSum_im_modEq' hχ hp8 hpin
end BandParity
