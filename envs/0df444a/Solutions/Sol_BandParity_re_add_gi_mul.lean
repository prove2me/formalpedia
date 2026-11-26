-- Prove2me | solution 1 for BandParity.re_add_gi_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:03:19.093504+00:00
-- url     : https://prove2.me/submissions/a7b1e532-c908-4475-aa71-86601709d342

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
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
omit hp hχ
namespace BandParity
theorem _root_.solution (a b : ℤ) : ((a : GaussianInt) + gi * b).re = a := by simp [gi]
end BandParity
