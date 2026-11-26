-- Prove2me | solution 1 for BandParity.two_mul_bijOn_gi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:20.986295+00:00
-- url     : https://prove2.me/submissions/beb60062-0348-48af-87ae-c1c35b1f5e21

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_bijOn_of_injOn_card
public import Theorems.Thm_BandParity_card_cls
public import Theorems.Thm_BandParity_two_mul_mapsTo_gi
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_P2M_BandParity_two_ne_zero__f8063a3397df
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
theorem _root_.solution (hp8 : p % 8 = 5) (hpin : χ 2 = gi) :
    Set.BijOn (fun x : ZMod p => 2 * x) (cls χ gi : Set (ZMod p))
      (cls χ (-1) : Set (ZMod p)) :=
  bijOn_of_injOn_card (two_mul_mapsTo_gi hpin)
    (fun _ _ _ _ h => mul_left_cancel₀ (two_ne_zero' (by omega)) h)
    (by rw [card_cls hχ (by simp), card_cls hχ (by simp)])
end BandParity
