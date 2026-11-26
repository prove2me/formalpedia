-- Prove2me | solution 1 for BandParity.lag_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:15:46.84825+00:00
-- url     : https://prove2.me/submissions/5e62f00a-0829-4a6d-8b4f-805ef446fa2b

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
public import Theorems.Thm_P2M_BandParity_lag_identity__1cd92334e44b


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
    ∑ u ∈ cls χ gi, parSign u * parSign (2 * u) = kappa p :=
  lag_identity' hχ hp8
end BandParity
