-- Prove2me | solution 1 for BandParity.sq_mapsTo_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:45.774037+00:00
-- url     : https://prove2.me/submissions/87420a5d-9407-48de-8be6-f0356abfa0af

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_mem_cls
public import Theorems.Thm_BandParity_gi_im
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
omit hχ
namespace BandParity
theorem _root_.solution : Set.MapsTo (fun x : ZMod p => x ^ 2) (cls χ 1 : Set (ZMod p))
    (cls χ 1 : Set (ZMod p)) := by
  intro u hu; rw [mem_cls] at hu ⊢; simp [map_pow, hu]
end BandParity
