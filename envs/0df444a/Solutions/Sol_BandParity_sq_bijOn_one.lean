-- Prove2me | solution 1 for BandParity.sq_bijOn_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:29.806807+00:00
-- url     : https://prove2.me/submissions/79c1b5d4-2de0-4f31-a4a3-4f335201f81c

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_bijOn_of_injOn_card
public import Theorems.Thm_BandParity_sq_injOn
public import Theorems.Thm_BandParity_sq_mapsTo_one

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
    Set.BijOn (fun x : ZMod p => x ^ 2) (cls χ 1 : Set (ZMod p)) (cls χ 1 : Set (ZMod p)) :=
  bijOn_of_injOn_card (sq_mapsTo_one) (sq_injOn hχ hp8 one_ne_zero) le_rfl
end BandParity
