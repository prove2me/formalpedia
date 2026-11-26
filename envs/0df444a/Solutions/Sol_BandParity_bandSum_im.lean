-- Prove2me | solution 1 for BandParity.bandSum_im
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:15:41.613633+00:00
-- url     : https://prove2.me/submissions/83068382-8f72-4783-aecd-d3685d2c2afb

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
public import Theorems.Thm_P2M_BandParity_bandSum_im__7ed5aaa03d73


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
    (bandSum χ).im = ∑ u ∈ cls χ gi, parSign u * parSign (u ^ 2) :=
  bandSum_im' hχ hp8
end BandParity
