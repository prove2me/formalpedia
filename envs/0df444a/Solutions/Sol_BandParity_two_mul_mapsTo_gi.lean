-- Prove2me | solution 1 for BandParity.two_mul_mapsTo_gi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:15.051891+00:00
-- url     : https://prove2.me/submissions/67d8ccbe-c791-4781-9c3e-113ba9dda37c

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_mem_cls
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_gi_sq
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
omit hχ
namespace BandParity
theorem _root_.solution (hpin : χ 2 = gi) :
    Set.MapsTo (fun x : ZMod p => 2 * x) (cls χ gi : Set (ZMod p))
      (cls χ (-1) : Set (ZMod p)) := by
  intro u hu; rw [mem_cls] at hu ⊢; simp only [map_mul, hu, hpin, ← sq, gi_sq]
end BandParity
