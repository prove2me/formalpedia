-- Prove2me | solution 1 for BandParity.sq_bijOn_gi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:18.957643+00:00
-- url     : https://prove2.me/submissions/14b76c12-b4c3-4bed-8f55-529a94b5d211

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_bijOn_of_injOn_card
public import Theorems.Thm_BandParity_card_cls
public import Theorems.Thm_BandParity_sq_injOn
public import Theorems.Thm_BandParity_sq_mapsTo_gi
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_ne_zero
public import Theorems.Thm_BandParity_gi_re
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



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
    Set.BijOn (fun x : ZMod p => x ^ 2) (cls χ gi : Set (ZMod p))
      (cls χ (-1) : Set (ZMod p)) :=
  bijOn_of_injOn_card (sq_mapsTo_gi) (sq_injOn hχ hp8 gi_ne_zero)
    (by rw [card_cls hχ (by simp), card_cls hχ (by simp)])
end BandParity
