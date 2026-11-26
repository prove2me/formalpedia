-- Prove2me | solution 1 for BandParity.bandSum_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:15:22.69992+00:00
-- url     : https://prove2.me/submissions/ccee5f51-4a46-4efd-933d-836e5ef34b82

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
public import Theorems.Thm_P2M_BandParity_bandSum_re__97b3040ddadc


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
    (bandSum χ).re = ∑ u ∈ cls χ 1, parSign u * parSign (u ^ 2) :=
  bandSum_re' hχ hp8
end BandParity
