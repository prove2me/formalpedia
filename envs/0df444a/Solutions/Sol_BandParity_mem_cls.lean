-- Prove2me | solution 1 for BandParity.mem_cls
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:05:25.353645+00:00
-- url     : https://prove2.me/submissions/36150cb5-5aa0-43c4-8407-63d6c633ccaf

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
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
theorem _root_.solution {z : GaussianInt} {x : ZMod p} : x ∈ (cls χ z : Set (ZMod p)) ↔ χ x = z := by
  simp
end BandParity
