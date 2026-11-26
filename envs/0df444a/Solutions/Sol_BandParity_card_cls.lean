-- Prove2me | solution 1 for BandParity.card_cls
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:05:10.044223+00:00
-- url     : https://prove2.me/submissions/044f3324-2840-46f7-a405-6b19f9b142ac

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_card_class


set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution {z : GaussianInt} (hz : z = 1 ∨ z = gi ∨ z = -1 ∨ z = -gi) :
    (cls χ z).card = (p - 1) / 4 := by
  have h := card_class hχ z hz
  change 4 * (cls χ z).card = p - 1 at h
  omega
end BandParity
