-- Prove2me | solution 1 for BandParity.coordinate_congruence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:18:35.9348+00:00
-- url     : https://prove2.me/submissions/c9f58f2e-84b1-4a2f-94b7-6be9b29a9d48

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
public import Theorems.Thm_P2M_BandParity_coordinate_congruence__0113bd6e318a


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
    kappa p ≡ Q p + k χ + t χ [ZMOD 4] :=
  coordinate_congruence' hχ hp8 hp5 hpin
end BandParity
